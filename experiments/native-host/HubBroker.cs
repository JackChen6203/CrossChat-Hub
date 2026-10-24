using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing;
using System.IO;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Threading;
using System.Web.Script.Serialization;
using System.Windows.Forms;

// Receives only the launching Hub HWND and bounded commands over private stdin.
// It has no socket, arbitrary binary launch or existing-chat attach interface.
internal static class HubBroker {
  [DllImport("user32.dll")] static extern IntPtr SetParent(IntPtr child, IntPtr parent);
  [DllImport("user32.dll")] static extern IntPtr GetParent(IntPtr window);
  [DllImport("user32.dll")] static extern IntPtr GetAncestor(IntPtr window, uint flags);
  [DllImport("user32.dll")] static extern bool IsWindow(IntPtr window);
  [DllImport("user32.dll")] static extern bool IsWindowVisible(IntPtr window);
  [DllImport("user32.dll")] static extern uint GetWindowThreadProcessId(IntPtr window, out uint pid);
  [DllImport("user32.dll", EntryPoint="GetWindowLongPtrW")] static extern IntPtr GetStyle(IntPtr window, int index);
  [DllImport("user32.dll", EntryPoint="SetWindowLongPtrW")] static extern IntPtr SetStyle(IntPtr window, int index, IntPtr value);
  [DllImport("user32.dll")] static extern bool GetWindowPlacement(IntPtr window, ref Placement placement);
  [DllImport("user32.dll")] static extern bool SetWindowPlacement(IntPtr window, ref Placement placement);
  [DllImport("user32.dll")] static extern bool MoveWindow(IntPtr window, int x, int y, int width, int height, bool repaint);
  [DllImport("user32.dll")] static extern bool GetClientRect(IntPtr window, out Rect rect);
  [DllImport("user32.dll")] static extern bool GetWindowRect(IntPtr window, out Rect rect);
  [DllImport("user32.dll")] static extern int MapWindowPoints(IntPtr from,IntPtr to,ref Rect points,uint count);
  [DllImport("user32.dll")] static extern bool ClientToScreen(IntPtr window,ref Point point);
  [DllImport("user32.dll")] static extern IntPtr GetWindowDpiAwarenessContext(IntPtr window);
  [DllImport("user32.dll")] static extern bool AreDpiAwarenessContextsEqual(IntPtr a, IntPtr b);
  [DllImport("user32.dll")] static extern IntPtr SetFocus(IntPtr window);
  [DllImport("user32.dll")] static extern bool ShowWindow(IntPtr window,int command);
  [DllImport("user32.dll")] static extern int SetThreadDpiHostingBehavior(int behavior);
  [DllImport("user32.dll")] static extern int GetWindowDpiHostingBehavior(IntPtr window);
  [StructLayout(LayoutKind.Sequential)] struct Placement { public int Length, Flags, ShowCmd; public Point Min, Max; public Rect Normal; }
  [StructLayout(LayoutKind.Sequential)] struct Rect { public int Left, Top, Right, Bottom; }
  static JavaScriptSerializer json=new JavaScriptSerializer { MaxJsonLength=4096, RecursionLimit=8 };
  static string nonce, resultPath, mode, injection;
  static Process controller, fixture; static long controllerStart, fixtureStart;
  static IntPtr hub, chat, hubStyle, chatStyle, chatParent, hubParent; static Placement chatPlacement,hubPlacement;
  static bool hubChanged,chatChanged,hubVisible,hubRestored,rollbackAttempted,rollbackVerified;
  static readonly List<string> rollbackOrder=new List<string>();
  static Form root; static Panel pane; static Label status;
#if LINE_PRODUCT
  static Button lineRecoveryButton, restoreLineButton;
#endif
  static bool attached, finish, closingRequested, resized, rootSurvived, chatSurvived, chatRestored, chatClosed, controllerExited, dpiEqual;
#if LINE_PRODUCT
  static bool closeRequestInFlight;
#endif
#if LINE_PRODUCT_FIXTURE
  static bool failNextFixtureRestore;
#endif
  static string error;
  static bool mixed; static int previousHosting=-1, rootHosting=-1,paneHosting=-1;
  static Rectangle rootWorkingArea;
  static string hubDpiBefore,hubDpiAfter,fixtureDpiBefore,fixtureDpiAfter,hubDpiRestored,fixtureDpiRestored;
  static readonly List<object> layoutObservations=new List<object>();
  static bool layoutAdapted;
  static int hubMinimumWidth,hubMinimumHeight;
  static Rect LocalBounds(IntPtr window) { Rect rect;if(!GetWindowRect(window,out rect))throw new Exception("Cannot read child bounds");MapWindowPoints(IntPtr.Zero,pane.Handle,ref rect,2);return rect; }
  static Rect WindowBounds(IntPtr window) { Rect rect;if(!GetWindowRect(window,out rect))throw new Exception("Cannot read native window bounds");return rect; }
  static object BoundsRecord(Rect r) {return new { left=r.Left,top=r.Top,width=r.Right-r.Left,height=r.Bottom-r.Top };}
#if LINE_STUDY || LINE_PRODUCT
  static readonly Stopwatch lineDeadline=new Stopwatch();
  static Rect lineOriginalBounds;
#endif
#if LINE_STUDY
  static bool lineDetachedSent;
#endif
#if LINE_STUDY || LINE_PRODUCT
  static bool LineAlive { get { return Alive(fixture,fixtureStart,chat); } }
#endif
#if LINE_STUDY
  static void DetachLine() {
    if(lineDetachedSent)return;
    try { RestoreFixture(); }
    catch(Exception ex) { error="LINE detach failed: "+ex.Message; }
    Save();
    status.Text=chatRestored ? "LINE restored. Waiting for isolated Hub exit." : "LINE restoration incomplete: broker root is retained. Use Detach LINE again.";
    Emit("line-detached","restored",chatRestored,"alive",LineAlive);
    if(chatRestored)lineDetachedSent=true;
  }
#endif
  static bool lineAttached, lineVisible;
#if LINE_PRODUCT
  static long lastSequence, currentSequence;
  static void RequestHostClose() {
    if(closeRequestInFlight)return;
    if(!attached||finish)return;
    closeRequestInFlight=true;closingRequested=true;Emit("close-request");
  }
#endif
  static void Trace(string stage) { File.AppendAllText(resultPath+".trace",DateTime.UtcNow.ToString("O")+" "+stage+Environment.NewLine); }
  static void Emit(string type, params object[] fields) {
    var record=new Dictionary<string,object> { {"v",1},{"nonce",nonce},{"type",type} };
#if LINE_PRODUCT
    record["sequence"]=currentSequence;
#endif
    for(int i=0;i<fields.Length;i+=2)record[(string)fields[i]]=fields[i+1];
    try { Console.WriteLine(json.Serialize(record)); Console.Out.Flush(); } catch(IOException) {}
  }
  static bool Alive(Process process,long start,IntPtr window) {
    uint pid; return process!=null && !process.HasExited && process.StartTime.ToUniversalTime().Ticks==start && IsWindow(window) && GetWindowThreadProcessId(window,out pid)!=0 && pid==(uint)process.Id;
  }
  static Placement PlacementOf(IntPtr hwnd) { var p=new Placement { Length=Marshal.SizeOf(typeof(Placement)) }; if(!GetWindowPlacement(hwnd,ref p))throw new Exception("Cannot save fixture placement"); return p; }
  static void Layout() {
#if LINE_STUDY
    if(chatRestored)return;
#endif
    if(!attached || finish || !Alive(controller,controllerStart,hub))return;
#if LINE_PRODUCT
    if(!lineAttached || !lineVisible) {
      if(!MoveWindow(hub,0,0,Math.Max(1,pane.ClientSize.Width),Math.Max(1,pane.ClientSize.Height),true))throw new Exception("Hub layout failed");
      if(lineAttached)ShowWindow(chat,0);
      return;
    }
#endif
    if(!Alive(fixture,fixtureStart,chat))return;
    // GetClientRect and MoveWindow both use the native physical coordinate
    // space of this PerMonitor process. Electron handles its own child DIP UI.
    Rect r; GetClientRect(pane.Handle,out r); int width=r.Right-r.Left,height=r.Bottom-r.Top;
    if(height<hubMinimumHeight)throw new Exception("Native pane is shorter than Hub minimum height");
    int chatWidth=
#if LINE_PRODUCT
      Math.Min(Math.Max(1,width/2),Math.Max(1,width-hubMinimumWidth));
#else
      360;
#endif
    for(int attempt=0;attempt<3;attempt++) {
      int left=width-chatWidth;
      if(left<hubMinimumWidth||chatWidth<1)throw new Exception("Native child minimum dimensions exceed available pane");
      if(!MoveWindow(hub,0,0,left,height,true)||!MoveWindow(chat,left,0,chatWidth,height,true))throw new Exception("Native layout failed");
      Rect observed=LocalBounds(chat),h=LocalBounds(hub),client;GetClientRect(chat,out client);
      Point origin=new Point(0,0);ClientToScreen(pane.Handle,ref origin);
      if(layoutObservations.Count>=16)layoutObservations.RemoveAt(0);
      layoutObservations.Add(new { attempt=attempt,requestedChatWidth=chatWidth,paneWidth=width,paneHeight=height,paneScreenX=origin.X,paneScreenY=origin.Y,hub=BoundsRecord(h),chat=BoundsRecord(observed),chatClient=BoundsRecord(client),chatStyle=GetStyle(chat,-16).ToInt64().ToString("x"),hubContext=DpiName(hub),chatContext=DpiName(chat) });
      // Verify outer rectangles in ONE parent-client coordinate space. No
      // clipped overflow is accepted merely because Windows hides it.
      if(h.Left==0&&h.Top==0&&observed.Top==0&&h.Right==observed.Left&&observed.Right==width&&h.Bottom==height&&observed.Bottom==height) { if(attempt>0)layoutAdapted=true;return; }
      int actualChat=observed.Right-observed.Left,actualHub=h.Right-h.Left;
      if(actualHub>left && actualHub+actualChat>width)throw new Exception("Native child minimum widths cannot fit side by side");
      if(actualChat!=chatWidth)chatWidth=actualChat;
      else if(actualHub>left)chatWidth=width-actualHub;
    }
    throw new Exception("Native layout did not converge within three read-back attempts");
  }
  static void RestoreFixture() {
    chatSurvived=Alive(fixture,fixtureStart,chat);
    if(!chatSurvived)return;
    SetParent(chat,chatParent); SetStyle(chat,-16,chatStyle); SetWindowPlacement(chat,ref chatPlacement);
    var actual=PlacementOf(chat);
    fixtureDpiRestored=DpiName(chat);
    chatRestored=GetParent(chat)==chatParent && GetStyle(chat,-16)==chatStyle && actual.Normal.Equals(chatPlacement.Normal) && actual.ShowCmd==chatPlacement.ShowCmd && IsWindowVisible(chat) && fixtureDpiRestored==fixtureDpiBefore;
#if LINE_STUDY || LINE_PRODUCT
    Rect bounds;GetWindowRect(chat,out bounds);chatRestored=chatRestored&&bounds.Equals(lineOriginalBounds);
    // This is the user's LINE process. NEVER close or terminate it.
#else
    if(chatRestored) { fixture.CloseMainWindow(); chatClosed=fixture.WaitForExit(5000); }
#endif
  }
  static bool RestoreHub() {
    if(!Alive(controller,controllerStart,hub))return false;
    SetParent(hub,hubParent); SetStyle(hub,-16,hubStyle); SetWindowPlacement(hub,ref hubPlacement);
    // An unshown Electron HWND may report SW_SHOWNORMAL in placement. Apply
    // saved visibility separately so rollback does not unexpectedly show it.
    ShowWindow(hub,hubVisible ? 4 : 0); SetStyle(hub,-16,hubStyle);
    var actual=PlacementOf(hub);
    hubDpiRestored=DpiName(hub);
    Trace("Hub rollback parent="+(GetParent(hub)==hubParent)+" style="+(GetStyle(hub,-16)==hubStyle)+" rect="+actual.Normal.Equals(hubPlacement.Normal)+" show="+actual.ShowCmd+"/"+hubPlacement.ShowCmd+" visible="+IsWindowVisible(hub)+"/"+hubVisible);
    return GetParent(hub)==hubParent && GetStyle(hub,-16)==hubStyle && actual.Normal.Equals(hubPlacement.Normal) && actual.ShowCmd==hubPlacement.ShowCmd && IsWindowVisible(hub)==hubVisible && hubDpiRestored==hubDpiBefore;
  }
  static void Inject(string point) { if(injection==point)throw new Exception("Injected failure: "+point); }
  static void Rollback() {
    rollbackAttempted=true;
    // Reverse mutation order. Never destroy the broker while a changed child
    // is still attached to it, even when attachment never reached 'attached'.
    if(chatChanged) { rollbackOrder.Add("fixture"); try { RestoreFixture(); }catch(Exception ex){Trace("fixture rollback error "+ex.Message);} }
    else if(fixture!=null && Alive(fixture,fixtureStart,chat)) {
#if LINE_STUDY || LINE_PRODUCT
      chatRestored=true;
#else
      fixture.CloseMainWindow(); chatClosed=fixture.WaitForExit(5000);
#endif
    }
    if(hubChanged) { rollbackOrder.Add("hub"); try { hubRestored=RestoreHub(); }catch(Exception ex){Trace("Hub rollback error "+ex.Message);} }
    rollbackVerified=(!chatChanged||chatRestored)&&(!hubChanged||hubRestored)
#if LINE_STUDY
      &&(fixture==null||LineAlive);
#elif LINE_PRODUCT
      &&(fixture==null||LineAlive);
#else
      &&(fixture==null||chatClosed);
#endif
  }
  static void Complete() {
    Trace("Complete entered");
    if(finish)return;
    rootSurvived=IsWindow(root.Handle)&&GetParent(root.Handle)==IntPtr.Zero;
    controllerExited=controller.HasExited;
#if LINE_PRODUCT
    if(chatChanged&&!chatRestored) { try { RestoreFixture(); } catch(Exception ex) { error="LINE recovery failed: "+ex.Message; } }
    if(chatRestored) { lineAttached=false;lineVisible=false;chatChanged=false; }
    try { hubRestored=RestoreHub(); } catch(Exception ex) { error="Hub recovery failed: "+ex.Message; }
    finish=true;
    if(!chatRestored && lineAttached) { error=error??"LINE may still be attached. Use the broker recovery button; do not force close this window."; if(lineRecoveryButton!=null)lineRecoveryButton.Visible=true; }
    status.Text=chatRestored ? "LINE restoration verified. Hub controller exited." : "LINE restoration is unverified. Keep this window open and retry.";
    Save();
    if(chatRestored||!chatChanged)root.Close();
#else
    RestoreFixture(); finish=true;
    status.Text="Controller exited. Fixture restored: "+chatRestored+". Broker root survived: "+rootSurvived;
    Save(); if(mode!="manual" || closingRequested)root.Close();
#endif
  }
#if LINE_PRODUCT
  static void AttachProductLine(Dictionary<string,object> d) {
    if(d.Count!=5 || !d.ContainsKey("sequence") ||
#if LINE_PRODUCT_FIXTURE
      !d.ContainsKey("fixture") || !Convert.ToBoolean(d["fixture"])
#else
      !d.ContainsKey("lineWitness")
#endif
      )throw new Exception("Invalid LINE attach request");
    if(lineAttached)throw new Exception("LINE is already attached");
    if(fixture!=null)fixture.Dispose();
#if LINE_PRODUCT_FIXTURE
    if(!d.ContainsKey("fixture") || Convert.ToBoolean(d["fixture"])!=true)throw new Exception("Owned fixture mode requires explicit fixture=true");
    fixture=Process.Start(new ProcessStartInfo(Application.ExecutablePath,"--fixture "+nonce) { UseShellExecute=false,CreateNoWindow=false });
    for(int i=0;i<100;i++) { fixture.Refresh(); chat=fixture.MainWindowHandle; if(chat!=IntPtr.Zero)break; Thread.Sleep(50); }
    chatRestored=false;fixtureStart=fixture.StartTime.ToUniversalTime().Ticks;
#else
    if(!d.ContainsKey("lineWitness"))throw new Exception("LINE witness is required");
    chatRestored=false;fixture=LineWitness.Validate((Dictionary<string,object>)d["lineWitness"],out chat);fixtureStart=fixture.StartTime.ToUniversalTime().Ticks;
#endif
    if(!Alive(fixture,fixtureStart,chat))throw new Exception("LINE window identity changed");
    chatParent=GetParent(chat);chatStyle=GetStyle(chat,-16);chatPlacement=PlacementOf(chat);GetWindowRect(chat,out lineOriginalBounds);
    fixtureDpiBefore=DpiName(chat);chatChanged=true;
    try {
      SetStyle(chat,-16,new IntPtr((chatStyle.ToInt64()|0x40000000L)&~0x80000000L));SetParent(chat,pane.Handle);
      fixtureDpiAfter=DpiName(chat);
      if(fixtureDpiAfter!="context-4" || GetParent(chat)!=pane.Handle || GetAncestor(chat,2)!=root.Handle)throw new Exception("LINE native parent or DPI verification failed");
      lineAttached=true;lineVisible=true;Layout();ShowWindow(chat,5);SetFocus(chat);Trace("product show visible="+IsWindowVisible(chat)+" root="+IsWindowVisible(root.Handle)+" pane="+IsWindowVisible(pane.Handle));
      if(!LayoutProductVerified())throw new Exception("LINE side-by-side layout read-back failed");
      Emit("line-attached","attached",true,"alive",LineAlive);
    } catch(Exception ex) {
      Trace("LINE attach rejected: "+ex.Message);
      try { RestoreFixture(); } catch {}
      if(chatRestored) { lineAttached=false;lineVisible=false;chatChanged=false; }
      else if(lineRecoveryButton!=null)lineRecoveryButton.Visible=true;
      Emit(chatRestored?"line-attach-failed":"line-restore-failed","restored",chatRestored,"alive",LineAlive,"message",ex.Message);
    }
  }
  static bool LayoutProductVerified() {
    Rect paneRect, hubRect, lineRect;GetClientRect(pane.Handle,out paneRect);GetWindowRect(hub,out hubRect);GetWindowRect(chat,out lineRect);
    var h=LocalBounds(hub);var l=LocalBounds(chat);
    bool parents=GetParent(hub)==pane.Handle&&GetParent(chat)==pane.Handle&&GetAncestor(hub,2)==root.Handle&&GetAncestor(chat,2)==root.Handle;
    bool edges=h.Left==0&&h.Top==0&&h.Right==l.Left&&l.Right==paneRect.Right&&h.Bottom==paneRect.Bottom&&l.Bottom==paneRect.Bottom&&l.Left>=hubMinimumWidth;
    bool visible=IsWindowVisible(chat);
    if(!parents||!edges||!visible)Trace("product layout readback failed parents="+parents+" edges="+edges+" visible="+visible+" rootVisible="+IsWindowVisible(root.Handle)+" paneVisible="+IsWindowVisible(pane.Handle)+" style="+GetStyle(chat,-16).ToInt64().ToString("x")+" hubMinimum="+hubMinimumWidth);
    return visible&&parents&&edges;
  }
  static bool LayoutProductHiddenVerified() {
    Rect paneRect;GetClientRect(pane.Handle,out paneRect);var h=LocalBounds(hub);
    bool verified=!IsWindowVisible(chat)&&GetParent(hub)==pane.Handle&&GetAncestor(hub,2)==root.Handle&&h.Left==0&&h.Top==0&&h.Right==paneRect.Right&&h.Bottom==paneRect.Bottom;
    if(!verified)Trace("product hidden layout readback failed visible="+IsWindowVisible(chat)+" hubParent="+(GetParent(hub)==pane.Handle)+" hubRoot="+(GetAncestor(hub,2)==root.Handle));
    return verified;
  }
  static void SetProductLineVisible(Dictionary<string,object> d,bool visible) {
    if(d.Count!=4||!d.ContainsKey("sequence")||!lineAttached||!LineAlive)throw new Exception("LINE is not attached");
    lineVisible=visible;
    if(visible)ShowWindow(chat,5);else ShowWindow(chat,0);
    Layout();
    Emit("line-visibility","visible",visible,"verified",visible?LayoutProductVerified():LayoutProductHiddenVerified());
  }
  static void DetachProductLine(Dictionary<string,object> d) {
    if(d.Count!=4||!d.ContainsKey("sequence"))throw new Exception("Invalid LINE detach request");
    if(!lineAttached) { Emit("line-detached","restored",true,"alive",true);return; }
    try { RestoreFixture(); } catch(Exception ex) { error="LINE restore failed: "+ex.Message; }
    bool aliveAfterRestore=LineAlive;
    if(chatRestored) { lineAttached=false;lineVisible=false;chatChanged=false;fixture.Dispose();fixture=null;chat=IntPtr.Zero;error=null;Layout(); }
    else { error=error??"LINE restoration read-back did not match the saved window state."; if(lineRecoveryButton!=null)lineRecoveryButton.Visible=true; }
    Emit(chatRestored?"line-detached":"line-restore-failed","restored",chatRestored,"alive",aliveAfterRestore,"message",error??"");
  }
  static void DetachProductHost(Dictionary<string,object> d) {
    if(d.Count!=4||!d.ContainsKey("sequence"))throw new Exception("Invalid detach-host request");
    if(lineAttached) {
#if LINE_PRODUCT_FIXTURE
      bool injectedFailure=failNextFixtureRestore;failNextFixtureRestore=false;
#endif
      try { RestoreFixture(); } catch(Exception ex) { error="LINE restore failed: "+ex.Message; }
#if LINE_PRODUCT_FIXTURE
      if(injectedFailure) { chatRestored=false;error="Owned fixture injected a one-time LINE restoration read-back failure.";rollbackVerified=false; }
#endif
      if(!chatRestored) { error=error??"LINE restoration read-back did not match the saved window state.";if(lineRecoveryButton!=null)lineRecoveryButton.Visible=true;Emit("line-restore-failed","restored",false,"alive",LineAlive,"message",error);return; }
      lineAttached=false;lineVisible=false;chatChanged=false;error=null;
    }
#if LINE_PRODUCT_FIXTURE
    if(fixture!=null&&chatRestored) { try { fixture.CloseMainWindow();fixture.WaitForExit(5000); } catch {} fixture.Dispose();fixture=null;chat=IntPtr.Zero; }
#else
    if(fixture!=null&&chatRestored) { fixture.Dispose();fixture=null;chat=IntPtr.Zero; }
#endif
    bool restoredHub=false;
    try { restoredHub=RestoreHub(); } catch(Exception ex) { error="Hub restore failed: "+ex.Message; }
    if(!restoredHub) { error=error??"Hub restoration read-back did not match the saved window state.";Emit("host-restore-failed","restored",false,"message",error);return; }
    hubChanged=false;finish=true;closingRequested=true;
    Emit("host-detached","restored",true,"lineAlive",true);
    root.Close();
  }
#endif
  static void Save() {
    Rect rootRect=new Rect(),paneRect=new Rect();if(root!=null&&root.IsHandleCreated)GetWindowRect(root.Handle,out rootRect);if(pane!=null&&pane.IsHandleCreated)GetWindowRect(pane.Handle,out paneRect);
    File.WriteAllText(resultPath,new JavaScriptSerializer { MaxJsonLength=65536,RecursionLimit=8 }.Serialize(new Dictionary<string,object> {
      {"attached",attached},{"sameRootAtAttach",attached},{"dpiAwarenessEqual",dpiEqual},{"resizeVerified",resized},
      {"controllerExited",controllerExited},{"brokerRootSurvived",rootSurvived},{"fixtureHwndSurvived",chatSurvived},
      {"fixtureRestoreVerified",chatRestored},{"fixtureNormallyClosed",chatClosed},{"error",error}
      ,{"injection",injection},{"hubChanged",hubChanged},{"fixtureChanged",chatChanged},{"rollbackAttempted",rollbackAttempted},
      {"hubRestoreVerified",hubRestored},{"hubAliveAtRollback",hubRestored&&Alive(controller,controllerStart,hub)},
      {"layoutObservations",layoutObservations},{"layoutAdapted",layoutAdapted},
#if LINE_PRODUCT
      {"layoutReport",new { root=BoundsRecord(rootRect),pane=BoundsRecord(paneRect),workingArea=new { left=rootWorkingArea.Left,top=rootWorkingArea.Top,width=rootWorkingArea.Width,height=rootWorkingArea.Height } }},
#endif
      {"hubMinimumWidth",hubMinimumWidth},{"hubMinimumHeight",hubMinimumHeight},
      {"rollbackVerified",rollbackVerified},{"rollbackOrder",rollbackOrder},
#if LINE_STUDY
      {"normalCycleCompleted",error==null&&finish&&chatRestored&&LineAlive},
      {"layoutVerified",resized},{"overallAccepted",error==null&&finish&&chatRestored&&LineAlive&&resized},
      {"realLineStudy",true},{"lineProcessAliveAfterRestore",LineAlive},{"lineElapsedMs",lineDeadline.ElapsedMilliseconds}
#else
      {"success",error==null&&finish&&chatRestored&&chatClosed&&resized}
#endif
      ,{"mixedHosting",mixed},{"previousThreadHosting",previousHosting},{"rootHosting",rootHosting},{"paneHosting",paneHosting},
      {"hubDpiBefore",hubDpiBefore},{"hubDpiAfter",hubDpiAfter},{"fixtureDpiBefore",fixtureDpiBefore},{"fixtureDpiAfter",fixtureDpiAfter},{"hubDpiRestored",hubDpiRestored},{"fixtureDpiRestored",fixtureDpiRestored},
      {"rootDpi",DpiName(root.Handle)},{"paneDpi",DpiName(pane.Handle)}
    }));
  }
  static void Fail(string message) {
    if(finish)return;
    error=message; Rollback(); finish=true;
#if LINE_PRODUCT
    if(chatChanged&&!chatRestored&&lineRecoveryButton!=null)lineRecoveryButton.Visible=true;
#endif
    status.Text=message+"; rollback verified: "+rollbackVerified;
    Save(); Emit("error","message",message,"rollbackVerified",rollbackVerified);
#if LINE_PRODUCT
    if(rollbackVerified)root.Close();
#endif
    // Keep root alive until controller consumes the failure acknowledgement
    // and exits. Closing it here can race Electron's close lifecycle and
    // return an incorrect startup exit code 0.
  }
  static string DpiName(IntPtr hwnd) {
    var context=GetWindowDpiAwarenessContext(hwnd);
    for(int i=1;i<=5;i++)if(AreDpiAwarenessContextsEqual(context,new IntPtr(-i)))return "context-"+i;
    return "unknown";
  }
  static void HandleLine(string line) {
    if(finish)return;
    var d=json.Deserialize<Dictionary<string,object>>(line);
    if(d==null || d.Count>
#if LINE_STUDY
      8
#elif LINE_PRODUCT
      8
#else
      7
#endif
      || !d.ContainsKey("v") || Convert.ToInt32(d["v"])!=1 || !d.ContainsKey("nonce") || (string)d["nonce"]!=nonce || !d.ContainsKey("type"))throw new Exception("Invalid broker envelope");
#if LINE_PRODUCT
    long incomingSequence;
    if(!d.ContainsKey("sequence")||!Int64.TryParse(Convert.ToString(d["sequence"]),out incomingSequence)||incomingSequence<=0||incomingSequence!=lastSequence+1)throw new Exception("Invalid broker command sequence");
    lastSequence=incomingSequence;currentSequence=incomingSequence;
#endif
    string type=(string)d["type"];
    Trace("command "+type);
    if(type=="attach" && !attached) {
      if(d.Count!=
#if LINE_STUDY
        8
#elif LINE_PRODUCT
        8
#else
        7
#endif
        || Convert.ToInt32(d["pid"])!=controller.Id || (string)d["startTicks"]!=controllerStart.ToString() || controller.HasExited || controller.StartTime.ToUniversalTime().Ticks!=controllerStart)throw new Exception("Controller identity mismatch");
      var minima=d["hubMinimum"] as Dictionary<string,object>;
      if(minima==null||minima.Count!=2||!minima.ContainsKey("width")||!minima.ContainsKey("height")||!(minima["width"] is int)||!(minima["height"] is int))throw new Exception("Invalid main-owned Hub minima");
      hubMinimumWidth=(int)minima["width"];hubMinimumHeight=(int)minima["height"];
      if(hubMinimumWidth<1||hubMinimumWidth>8192||hubMinimumHeight<1||hubMinimumHeight>8192)throw new Exception("Hub minima outside bounded range");
#if LINE_PRODUCT
      root.PerformLayout();
      int productMinimumWidth=checked(hubMinimumWidth+360+(root.Width-root.ClientSize.Width));
      int productMinimumHeight=checked(hubMinimumHeight+(root.Height-pane.ClientSize.Height));
      if(productMinimumWidth>rootWorkingArea.Width||productMinimumHeight>rootWorkingArea.Height)throw new Exception("Native root minimum dimensions exceed the selected display working area; attachment refused");
      root.MinimumSize=new Size(productMinimumWidth,productMinimumHeight);
      root.Size=new Size(Math.Max(root.Width,productMinimumWidth),Math.Max(root.Height,productMinimumHeight));
      if(root.Width>rootWorkingArea.Width||root.Height>rootWorkingArea.Height)throw new Exception("Native root minimum dimensions exceed the selected display working area; attachment refused");
      root.Location=new Point(rootWorkingArea.Left+Math.Max(0,(rootWorkingArea.Width-root.Width)/2),rootWorkingArea.Top+Math.Max(0,(rootWorkingArea.Height-root.Height)/2));
#endif
      long raw; if(!long.TryParse((string)d["hwnd"],out raw)||raw<=0)throw new Exception("Invalid HWND"); hub=new IntPtr(raw);
      if(!Alive(controller,controllerStart,hub)||GetParent(hub)!=IntPtr.Zero)throw new Exception("Hub HWND ownership/root mismatch");
      dpiEqual=AreDpiAwarenessContextsEqual(GetWindowDpiAwarenessContext(hub),GetWindowDpiAwarenessContext(root.Handle));
      hubDpiBefore=DpiName(hub);
      if(mixed) {
        if(hubDpiBefore!="context-3"||DpiName(root.Handle)!="context-4"||DpiName(pane.Handle)!="context-4"||rootHosting!=1||paneHosting!=1)throw new Exception("Mixed owned-study DPI prerequisites failed");
      } else if(!dpiEqual)throw new Exception("DPI awareness differs (Hub="+DpiName(hub)+", broker="+DpiName(root.Handle)+"); embedding refused");
      hubParent=GetParent(hub); hubStyle=GetStyle(hub,-16);hubPlacement=PlacementOf(hub);hubVisible=IsWindowVisible(hub);
#if LINE_STUDY
      if(!mixed||injection!="none"||mode!="manual")throw new Exception("Real LINE study only supports normal manual mixed hosting");
      fixture=LineWitness.Validate((Dictionary<string,object>)d["lineWitness"],out chat);fixtureStart=fixture.StartTime.ToUniversalTime().Ticks;
      if(lineDeadline.ElapsedMilliseconds>8000)throw new Exception("LINE witness was too slow; refusing attachment");
#elif LINE_PRODUCT
      if(!mixed||injection!="none"||mode!="manual")throw new Exception("Product LINE host requires mixed normal mode");
#else
      fixture=Process.Start(new ProcessStartInfo(Application.ExecutablePath,"--fixture "+nonce) { UseShellExecute=false }); fixtureStart=fixture.StartTime.ToUniversalTime().Ticks;
      for(int i=0;i<100;i++) { fixture.Refresh(); chat=fixture.MainWindowHandle; if(chat!=IntPtr.Zero)break; Thread.Sleep(50); }
#endif
#if !LINE_PRODUCT
      if(!Alive(fixture,fixtureStart,chat))throw new Exception("Owned fixture has no HWND");
      chatParent=GetParent(chat); chatStyle=GetStyle(chat,-16); chatPlacement=PlacementOf(chat);
#endif
#if LINE_STUDY || LINE_PRODUCT
      if(fixture!=null) {
      GetWindowRect(chat,out lineOriginalBounds);
      fixtureDpiBefore=DpiName(chat);
      if(mixed&&fixtureDpiBefore!="context-4")throw new Exception("Owned fixture is not PMv2");
      }
#endif
      hubChanged=true; SetStyle(hub,-16,new IntPtr((hubStyle.ToInt64()|0x40000000L)&~0x80000000L)); SetParent(hub,pane.Handle); Inject("after-hub-parent");
      hubDpiAfter=DpiName(hub);
      Trace("hub parent set rootVisible="+IsWindowVisible(root.Handle)+" paneVisible="+IsWindowVisible(pane.Handle)+" hubVisible="+IsWindowVisible(hub));
      if(hubDpiAfter!=hubDpiBefore)throw new Exception("Hub DPI changed during parenting");
#if !LINE_PRODUCT
      chatChanged=true; SetStyle(chat,-16,new IntPtr((chatStyle.ToInt64()|0x40000000L)&~0x80000000L)); SetParent(chat,pane.Handle); Inject("after-fixture-parent");
      fixtureDpiAfter=DpiName(chat);
      if(fixtureDpiAfter!=fixtureDpiBefore)throw new Exception("Fixture DPI changed during parenting");
      if(GetParent(hub)!=pane.Handle || GetParent(chat)!=pane.Handle || GetAncestor(hub,2)!=root.Handle || GetAncestor(chat,2)!=root.Handle)throw new Exception("Shared broker root verification failed");
#else
      if(GetParent(hub)!=pane.Handle || GetAncestor(hub,2)!=root.Handle)throw new Exception("Hub broker root verification failed");
#endif
      attached=true;
#if LINE_PRODUCT
      restoreLineButton.Enabled=true;
#endif
      Layout(); Inject("after-resize"); status.Text=
#if LINE_STUDY
      "Real LINE window temporarily embedded. Automatic detach within 20 seconds; no messaging operations.";
#elif LINE_PRODUCT
      "Hub is hosted; LINE remains outside until explicitly enabled.";
#else
      "Isolated actual Hub + owned synthetic chat. No LINE account attached.";
#endif
      Trace("attached root="+root.Handle+" brokerPid="+Process.GetCurrentProcess().Id+(fixture==null?"":" fixturePid="+fixture.Id)); Save();
#if LINE_PRODUCT
      Emit("attached","rootHwnd",root.Handle.ToInt64().ToString(),"layoutReport",new { root=BoundsRecord(WindowBounds(root.Handle)),pane=BoundsRecord(WindowBounds(pane.Handle)),workingArea=new { left=rootWorkingArea.Left,top=rootWorkingArea.Top,width=rootWorkingArea.Width,height=rootWorkingArea.Height } });
#else
      Emit("attached","rootHwnd",root.Handle.ToInt64().ToString());
#endif
    } else if(type=="shutdown" && d.Count==
#if LINE_PRODUCT
      4
#else
      3
#endif
      ) { closingRequested=true;
#if LINE_STUDY
      DetachLine();
#endif
      status.Text="Waiting for Hub session flush and exit; broker stays alive.";
#if LINE_PRODUCT
      Emit("shutdown-ack","accepted",true);
#endif
    }
#if LINE_PRODUCT
    else if(type=="line-attach") { AttachProductLine(d); }
    else if(type=="line-detach") { DetachProductLine(d); }
    else if(type=="line-show") { SetProductLineVisible(d,true); }
    else if(type=="line-hide") { SetProductLineVisible(d,false); }
    else if(type=="detach-host") { DetachProductHost(d); }
    else if(type=="close-request-cancel"&&d.Count==4) { closeRequestInFlight=false;closingRequested=false;Emit("close-request-cancelled","released",true); }
#if LINE_PRODUCT_FIXTURE
    else if(type=="fixture-root-close"&&d.Count==4) { root.Close();root.Close();Emit("fixture-root-close","accepted",true); }
    else if(type=="fixture-click-restore-button"&&d.Count==4) { restoreLineButton.PerformClick();Emit("fixture-restore-button","accepted",true); }
    else if(type=="fixture-fail-next-restore"&&d.Count==4) { failNextFixtureRestore=true;Emit("fixture-fail-next-restore","accepted",true); }
#endif
#endif
    else if(type=="resize-check" && d.Count==3 && attached) {
      root.Size=new Size(root.Width+80,root.Height+40); Layout();
      Rect a,b,c; GetClientRect(pane.Handle,out a); GetWindowRect(hub,out b); GetWindowRect(chat,out c);
      Trace("resize pane="+a.Right+","+a.Bottom+" hub="+b.Left+","+b.Top+","+b.Right+","+b.Bottom+" chat="+c.Left+","+c.Top+","+c.Right+","+c.Bottom);
      resized=(b.Right-b.Left)+(c.Right-c.Left)==a.Right && b.Bottom-b.Top==a.Bottom && c.Bottom-c.Top==a.Bottom && b.Right==c.Left && b.Top==c.Top && GetAncestor(hub,2)==root.Handle && GetAncestor(chat,2)==root.Handle;
      Emit("resized","verified",resized); Save();
    } else throw new Exception("Unexpected broker command");
  }
  [STAThread] static int Main(string[] args) {
#if LINE_PRODUCT
    // Keep this exact-argument protocol probe ahead of WinForms initialization,
    // DPI hosting changes, process lookup, witness capture, and HWND access.
    if(Array.IndexOf(args,"--self-test")>=0) {
      if(args.Length!=1||args[0]!="--self-test")return 2;
      try {
        Console.SetOut(new StreamWriter(Console.OpenStandardOutput(),new System.Text.UTF8Encoding(false)) { AutoFlush=true });
        var probe=json.DeserializeObject(json.Serialize(new {v=1,type="ready",protocol=1})) as Dictionary<string,object>;
        if(probe==null||Convert.ToInt32(probe["v"])!=1||Convert.ToInt32(probe["protocol"])!=1)return 1;
        Console.WriteLine(json.Serialize(new {ok=true,protocol=1,runtime=Environment.Version.ToString(),helperKind="line-product-broker"}));
        return 0;
      } catch { return 1; }
    }
#endif
    Application.EnableVisualStyles();
    chatClosed=false;
    if(args.Length==2 && args[0]=="--fixture" && Regex.IsMatch(args[1],"^[a-f0-9]{48}$")) {
      int minimumWidth=0;string minimum=Environment.GetEnvironmentVariable("CROSSCHAT_BROKER_OWNED_MIN_WIDTH");
      if(minimum!=null&&(!int.TryParse(minimum,out minimumWidth)||minimumWidth<128||minimumWidth>1600))return 2;
      Application.Run(new Form { Text="Owned synthetic native chat",Width=360,Height=450,MinimumSize=new Size(minimumWidth,0),Controls={ new Label { Text="Native chat fixture\n\nNo LINE or Chrome process.\n\nThis HWND is a sibling of the actual Hub.\nBroker owns the shared top-level root.",Dock=DockStyle.Fill,Padding=new Padding(20),Font=new Font("Segoe UI",12) } } }); return 0;
    }
    int pid;
    if(args.Length!=6 || !int.TryParse(args[0],out pid) || pid<=0 || !Regex.IsMatch(args[1],"^[a-f0-9]{48}$") || !Path.IsPathRooted(args[2]) || Path.GetFileName(args[2])!="broker-result.json" ||
#if LINE_PRODUCT
      !Path.GetFileName(Path.GetDirectoryName(args[2])).StartsWith("crosschat-native-line-") ||
#else
      !Path.GetFileName(Path.GetDirectoryName(args[2])).StartsWith("crosschat-broker-hub-") ||
#endif
      (args[3]!="normal"&&args[3]!="crash"&&args[3]!="manual") || !Regex.IsMatch(args[4],"^(none|after-hub-parent|after-fixture-parent|after-resize|stdio-eof)$") || (args[5]!="strict-v1"&&args[5]!="mixed-v2"))return 2;
    nonce=args[1];resultPath=args[2];mode=args[3];injection=args[4]; controller=Process.GetProcessById(pid); controllerStart=controller.StartTime.ToUniversalTime().Ticks;
    mixed=args[5]=="mixed-v2";
    if(mixed) { try { previousHosting=SetThreadDpiHostingBehavior(1); }catch(EntryPointNotFoundException){return 3;} if(previousHosting==-1)return 3; }
    AppDomain.CurrentDomain.UnhandledException+=delegate(object s,UnhandledExceptionEventArgs e){Trace("unhandled "+e.ExceptionObject);};
    Trace("start brokerPid="+Process.GetCurrentProcess().Id+" controller="+pid);
    IntPtr controllerWindow=controller.MainWindowHandle;
    if(controllerWindow==IntPtr.Zero)return 4;
    var targetScreen=Screen.FromHandle(controllerWindow);rootWorkingArea=targetScreen.WorkingArea;
    root=new Form { Text=
#if LINE_PRODUCT
      "CrossChat Hub — native LINE host",
#else
      "CrossChat broker — isolated actual Hub study",
#endif
      Width=Math.Min(1660,rootWorkingArea.Width),Height=Math.Min(900,rootWorkingArea.Height),StartPosition=FormStartPosition.Manual };
    root.MaximumSize=rootWorkingArea.Size;
    root.Location=new Point(rootWorkingArea.Left+Math.Max(0,(rootWorkingArea.Width-root.Width)/2),rootWorkingArea.Top+Math.Max(0,(rootWorkingArea.Height-root.Height)/2));
    status=new Label { Dock=DockStyle.Top,Height=34,Text="Waiting for isolated Hub handshake",Padding=new Padding(6) };
    var toolbar=new FlowLayoutPanel { Dock=DockStyle.Top,Height=36 };
    var focusHub=new Button { Text="Focus Hub",Width=120 }; focusHub.Click+=delegate { if(attached&&!finish)Emit("focus-hub"); };
    var focusChat=new Button { Text="Focus fixture",Width=120 }; focusChat.Click+=delegate { if(Alive(fixture,fixtureStart,chat))SetFocus(chat); };
    toolbar.Controls.Add(focusHub);toolbar.Controls.Add(focusChat);
#if LINE_STUDY
    focusChat.Visible=false;
    var detach=new Button { Text="Detach LINE now",Width=150 };detach.Click+=delegate {DetachLine();};toolbar.Controls.Add(detach);
    root.Text="CrossChat broker — temporary LINE study";
#endif
#if LINE_PRODUCT
    restoreLineButton=new Button { Text="還原 LINE",Width=130,Enabled=false };
    restoreLineButton.Click+=delegate { RequestHostClose(); };
    toolbar.Controls.Add(restoreLineButton);
    lineRecoveryButton=new Button { Text="Retry LINE restoration",Width=190,Visible=false };
    lineRecoveryButton.Click+=delegate {
      try { RestoreFixture(); } catch(Exception ex) { error="LINE recovery failed: "+ex.Message; }
      if(chatRestored) { lineAttached=false;lineVisible=false;chatChanged=false;error=null;status.Text="LINE restoration verified.";Save(); if(controller.HasExited)root.Close();else Layout(); }
      else status.Text="LINE restoration is unverified. Keep this window open and retry.";
    };
    toolbar.Controls.Add(lineRecoveryButton);
#endif
    pane=new Panel { Dock=DockStyle.Fill }; root.Controls.Add(pane);root.Controls.Add(status);root.Controls.Add(toolbar);
    // Force creation of both native parent HWNDs while MIXED is active, then
    // restore the thread setting. Existing windows are never retrofitted.
    IntPtr rootHandle=root.Handle,paneHandle=pane.Handle;
    if(mixed) { rootHosting=GetWindowDpiHostingBehavior(rootHandle);paneHosting=GetWindowDpiHostingBehavior(paneHandle);SetThreadDpiHostingBehavior(previousHosting); }
    root.Resize+=delegate { try { Layout(); }catch(Exception ex){Fail(ex.Message);} };
    root.FormClosing+=delegate(object sender,FormClosingEventArgs e) {
      if(error!=null && !rollbackVerified && ((IsWindow(hub)&&GetAncestor(hub,2)==root.Handle)||(IsWindow(chat)&&GetAncestor(chat,2)==root.Handle))) {
        e.Cancel=true;
#if LINE_PRODUCT
        if(!controller.HasExited)RequestHostClose();
#endif
        return;
      }
#if LINE_STUDY
      if(!chatRestored&&chatChanged) {e.Cancel=true;DetachLine();return;}
#elif LINE_PRODUCT
      if(chatChanged&&!chatRestored) {e.Cancel=true;status.Text="LINE is not restored. Keep this root open and retry LINE restoration.";if(!controller.HasExited)RequestHostClose();return;}
#endif
      if(!finish && !controller.HasExited) {
        e.Cancel=true;
#if LINE_PRODUCT
        RequestHostClose();
#else
        if(!closingRequested){closingRequested=true;Emit("close-request");}
#endif
      }
    };
    root.FormClosed+=delegate {Trace("root closed finish="+finish);};
    var timer=new System.Windows.Forms.Timer { Interval=100 };
    timer.Tick+=delegate {
#if LINE_STUDY
      if(!finish&&attached&&!chatRestored&&lineDeadline.ElapsedMilliseconds>=20000)DetachLine();
#endif
      if(finish && error!=null && rollbackVerified && controller.HasExited) { root.Close(); return; }
      if(!finish && controller.HasExited) { try { Complete(); } catch(Exception ex){Fail(ex.Message);} }
    };
    root.Shown+=delegate {
      ShowWindow(root.Handle,5);ShowWindow(pane.Handle,5);
      Trace("root shown event visible="+IsWindowVisible(root.Handle)+" paneVisible="+IsWindowVisible(pane.Handle)+" managedVisible="+root.Visible);
#if LINE_STUDY
      lineDeadline.Start();
#endif
      Emit("ready","startTicks",controllerStart.ToString()); timer.Start();
      new Thread(delegate() { try {
        // Bound each line before allocation; read only the private inherited pipe.
        var line=new System.Text.StringBuilder(); int ch;
        while((ch=Console.In.Read())!=-1) { if(ch=='\n') { string copy=line.ToString().TrimEnd('\r'); line.Length=0; root.BeginInvoke((Action)delegate { try { HandleLine(copy); }catch(Exception ex){Fail(ex.Message);} }); } else { if(line.Length>=4096)throw new Exception("Broker input line exceeds limit");line.Append((char)ch); } }
        root.BeginInvoke((Action)delegate { if(!finish&&!closingRequested)Fail("Broker stdin EOF"); });
      } catch(Exception ex) { try { root.BeginInvoke((Action)delegate { Fail(ex.Message); }); }catch(InvalidOperationException){} } }) { IsBackground=true }.Start();
    };
    Application.Run(root);timer.Dispose();controller.Dispose();
#if LINE_PRODUCT_FIXTURE
    if(fixture!=null&&chatRestored&&!fixture.HasExited) { try { fixture.CloseMainWindow();fixture.WaitForExit(5000); } catch {} }
#endif
    if(fixture!=null)fixture.Dispose();
    return error==null ? 0 : 1;
  }
}
