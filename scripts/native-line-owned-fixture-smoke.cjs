'use strict';
// Exercises the LINE_PRODUCT lifecycle against an owned synthetic HWND only.
const { app, BrowserWindow, screen } = require('electron');
const { spawn } = require('node:child_process');
const crypto = require('node:crypto');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');

if (process.platform !== 'win32') throw new Error('Owned native broker smoke is Windows-only');
const binary = process.env.CROSSCHAT_PRODUCT_BROKER_FIXTURE || path.join(__dirname, '..', 'build', 'bin', 'native-host', 'ProductBrokerFixture.exe');
if (!fs.existsSync(binary)) throw new Error('Build native helpers before running the owned fixture smoke');
const forceNoFit = process.env.CROSSCHAT_FIXTURE_NO_FIT === '1';
const layoutBoundary = process.env.CROSSCHAT_FIXTURE_LAYOUT_BOUNDARY || '';
const folder = fs.mkdtempSync(path.join(os.tmpdir(), 'crosschat-native-line-'));
const nonce = crypto.randomBytes(24).toString('hex');
let window, child, sequence = 0, output = '', settled = false, timer, closeRequestCount = 0;
const pending = new Map();
function send(type, fields = {}) {
  const current = ++sequence;
  return new Promise((resolve, reject) => {
    pending.set(current, { resolve, reject });
    child.stdin.write(JSON.stringify({ v: 1, nonce, sequence: current, type, ...fields }) + '\n');
  });
}
function fail(error) {
  if (settled) return;
  settled = true; clearTimeout(timer);
  for (const item of pending.values()) item.reject(error);
  pending.clear();
  console.error('FAIL: owned native LINE lifecycle smoke:', error.message);
  if (!child || child.exitCode !== null) { window?.destroy(); app.exit(1); return; }
  // EOF asks the broker to roll back the owned fixture. No live LINE is involved.
  child.stdin.end();
  const fallback = setTimeout(() => { window?.destroy(); app.exit(1); }, 10000);
  child.once('exit', () => { clearTimeout(fallback); window?.destroy(); app.exit(1); });
}
async function run() {
  window = new BrowserWindow({ show: false, width: 1200, height: 800, minWidth: 800, minHeight: 600, webPreferences: { sandbox: true, nodeIntegration: false, contextIsolation: true } });
  await window.loadURL('data:text/html,<title>Owned native broker fixture</title><main>Offline fixture only</main>');
  window.show();
  const handle = window.getNativeWindowHandle();
  const hwnd = (handle.length === 8 ? handle.readBigUInt64LE() : BigInt(handle.readUInt32LE())).toString();
  const minimum = window.getMinimumSize();
  const scale = screen.getDisplayMatching(window.getBounds()).scaleFactor;
  const hubMinimum = { width: Math.ceil(minimum[0] * scale), height: Math.ceil(minimum[1] * scale) };
  child = spawn(binary, [String(process.pid), nonce, path.join(folder, 'broker-result.json'), 'manual', 'none', 'mixed-v2'], { stdio: ['pipe', 'pipe', 'pipe'], detached: true, windowsHide: true });
  child.stderr.on('data', bytes => process.stderr.write(bytes));
  child.stdout.on('data', bytes => {
    output += bytes.toString('utf8');
    if (output.length > 65536) { fail(new Error('broker output exceeded limit')); return; }
    let index;
    while ((index = output.indexOf('\n')) >= 0) {
      const line = output.slice(0, index); output = output.slice(index + 1);
      let message;
      try { message = JSON.parse(line); } catch { fail(new Error('invalid broker JSON')); return; }
      if (message.v !== 1 || message.nonce !== nonce || !Number.isSafeInteger(message.sequence)) { fail(new Error('invalid broker envelope')); return; }
      if (message.type === 'ready') {
        if (forceNoFit) {
          void send('attach', { pid: process.pid, startTicks: message.startTicks, hwnd, hubMinimum: { width: 8192, height: 8192 } })
            .then(result => {
              if (result.type !== 'error' || !/working area; attachment refused/.test(result.message) || result.rollbackVerified !== true) throw new Error(`No-fit attach was not rejected and rolled back: ${JSON.stringify(result)}`);
              settled = true; clearTimeout(timer); child.stdin.end();
            }).catch(fail);
          return;
        }
        void send('attach', { pid: process.pid, startTicks: message.startTicks, hwnd, hubMinimum })
          .then(result => {
            if (result.type !== 'attached') throw new Error('Hub attach was not acknowledged');
            const layout = result.layoutReport;
            if (!layout || !layout.root || !layout.pane || !layout.workingArea) throw new Error('Safe root/pane/working-area geometry report is missing');
            const inside = (r, bounds) => r.left >= bounds.left && r.top >= bounds.top && r.left + r.width <= bounds.left + bounds.width && r.top + r.height <= bounds.top + bounds.height;
            if (!inside(layout.root, layout.workingArea) || !inside(layout.pane, layout.root)) throw new Error('Native root or pane is outside its verified working-area/root bounds');
            if ('hwnd' in layout.root || 'title' in layout.root || 'text' in layout.root) throw new Error('Geometry report contains disallowed metadata');
            return send('line-attach', { fixture: true });
          }).then(result => {
            if (layoutBoundary) {
              if (layoutBoundary === 'exact-fit') {
                if (result.type !== 'line-attached' || result.attached !== true || result.alive !== true || result.layoutAdapted !== true) throw new Error(`Exact-fit owned layout failed: ${JSON.stringify(result)}`);
                const observations = result.layoutObservations;
                const last = observations?.at(-1), prior = observations?.at(-2);
                if (!last || !prior || last.chat.width !== 364 || last.hub.width < hubMinimum.width || last.hub.left !== 0 || last.hub.left + last.hub.width !== last.chat.left || last.chat.left + last.chat.width !== last.paneWidth || last.paneWidth <= prior.paneWidth) throw new Error(`Exact-fit outer-rectangle expansion/readback failed: ${JSON.stringify({ prior, last })}`);
                const root = result.root, workingArea = result.workingArea;
                if (!root || !workingArea || root.left < workingArea.left || root.top < workingArea.top || root.left + root.width > workingArea.left + workingArea.width || root.top + root.height > workingArea.top + workingArea.height) throw new Error(`Expanded root escaped its working area: ${JSON.stringify({ root, workingArea })}`);
              } else if (layoutBoundary === 'one-pixel-short') {
                if (result.type !== 'line-attach-failed' || result.restored !== true || !/cannot fit within the selected display working area/.test(result.message)) throw new Error(`One-pixel-short layout was not rejected and restored: ${JSON.stringify(result)}`);
              } else throw new Error(`Unknown fixture layout boundary mode: ${layoutBoundary}`);
              return send('detach-host');
            }
            if (result.type !== 'line-attached' || result.attached !== true || result.alive !== true) throw new Error(`Owned fixture attach/readback failed: ${JSON.stringify(result)}`);
            return send('line-hide');
          }).then(result => {
            if (layoutBoundary) {
              if (result.type !== 'host-detached' || result.restored !== true || result.lineAlive !== true) throw new Error(`Boundary fixture host cleanup failed: ${JSON.stringify(result)}`);
              settled = true; clearTimeout(timer); child.stdin.end();
              return;
            }
            if (result.type !== 'line-visibility' || result.visible !== false || result.verified !== true) throw new Error('Owned fixture hide/readback failed');
            return send('line-show');
          }).then(result => {
            if (result.type !== 'line-visibility' || result.visible !== true || result.verified !== true) throw new Error('Owned fixture show/readback failed');
            return send('fixture-fail-next-restore');
          }).then(result => {
            if (result.type !== 'fixture-fail-next-restore' || result.accepted !== true) throw new Error('Owned fixture restore-failure setup failed');
            return send('fixture-click-restore-button');
          }).then(result => {
            if (result.type !== 'fixture-restore-button' || result.accepted !== true || closeRequestCount !== 1) throw new Error('Native restore button did not emit exactly one close-request');
            return send('detach-host');
          }).then(result => {
            if (result.type !== 'line-restore-failed' || result.restored !== false) throw new Error('Owned fixture restore-failure response was not retained for retry');
            return send('close-request-cancel');
          }).then(result => {
            if (result.type !== 'close-request-cancelled' || result.released !== true) throw new Error('Close-request retry release was not acknowledged');
            return send('fixture-click-restore-button');
          }).then(result => {
            if (result.type !== 'fixture-restore-button' || result.accepted !== true || closeRequestCount !== 2) throw new Error('Native restore button retry did not emit one new close-request');
            return send('detach-host');
          }).then(result => {
            if (result.type !== 'host-detached' || result.restored !== true || result.lineAlive !== true) throw new Error('Owned fixture normal detach/readback failed');
            settled = true; clearTimeout(timer); child.stdin.end();
          }).catch(fail);
      } else if (message.type === 'close-request') {
        closeRequestCount++;
      } else {
        const request = pending.get(message.sequence);
        if (request) { pending.delete(message.sequence); request.resolve(message); }
      }
    }
  });
  child.once('error', fail);
  child.once('exit', code => {
    if (!settled || (code !== 0 && !(forceNoFit && code === 1))) { fail(new Error(`native helper exited before clean completion (${code})`)); return; }
    window.destroy(); console.log(forceNoFit
      ? 'PASS: ProductBrokerFixture rejected no-fit attachment and verified rollback; no LINE process used.'
      : layoutBoundary
        ? `PASS: ProductBrokerFixture ${layoutBoundary} actual-outer-width layout and restoration; no LINE process used.`
      : 'PASS: ProductBrokerFixture attach/show/hide/native restore-button retry/detach readbacks and working-area containment; no LINE process used.'); app.exit(0);
  });
  timer = setTimeout(() => fail(new Error('owned fixture lifecycle timed out')), 30000);
}
app.whenReady().then(run).catch(fail);
