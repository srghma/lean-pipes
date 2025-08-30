import Std.Sync.Channel
import Std.Internal.Async
import Std.Time

/-- Helper for logging with relative ms since `start`. -/
def logWithTime (start : Nat) (tag msg : String) : IO Unit := do
  let now ← IO.monoMsNow
  let elapsed := now - start
  IO.println s!"[+{elapsed}ms][{tag}] {msg}"

/-- main loop that selects on two channels -/
def loop (stepsLeft : Nat) (ch1 ch2 : Std.CloseableChannel Nat) (start : Nat)
    : IO (Std.Internal.IO.Async.AsyncTask Unit) := do
  let ch1c ← ch1.isClosed
  let ch2c ← ch2.isClosed
  logWithTime start "loop" s!"stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}"

  if stepsLeft <= 0 then
    logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" "max steps reached, exiting loop"
    return Std.Internal.IO.Async.AsyncTask.pure .unit
  else if ch1c && ch2c then
    logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" "both channels closed, exiting loop"
    return Std.Internal.IO.Async.AsyncTask.pure .unit
  else
    let stepsLeft' := stepsLeft - 1
    let mut cases := #[]
    if !ch1c then
      cases := cases.push <|
        .case ch1.recvSelector fun msg? => do
          logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" s!"rx1 got {msg?}"
          loop stepsLeft' ch1 ch2 start
    if !ch2c then
      cases := cases.push <|
        .case ch2.recvSelector fun msg? => do
          logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" s!"rx2 got {msg?}"
          loop stepsLeft' ch1 ch2 start
    logWithTime start s!"loop stepsLeft={stepsLeft}, ch1c={ch1c}, ch2c={ch2c}" "starting select"
    Std.Internal.IO.Async.Selectable.one cases

def main : IO Unit := do
  let start ← IO.monoMsNow -- reference time

  let ch1 ← Std.CloseableChannel.new (some 10)
  let ch2 ← Std.CloseableChannel.new (some 10)

  let t1 : Std.Internal.IO.Async.Async Unit := do
    let send (n: Nat) := do logWithTime start "t1" s!"waiting 100 before sending {n}"; IO.sleep 100; logWithTime start "t1" s!"sending {n}"; ch1.sync.send n
    logWithTime start "t1" "sending 1"; ch1.sync.send 1
    send 2
    logWithTime start "t1" "waiting 100 before closing channel"; IO.sleep 100; logWithTime start "t1" "closing channel"; ch1.close
    logWithTime start "t1" "closed"

  let t2 : Std.Internal.IO.Async.Async Unit := do
    let send (n: Nat) := do logWithTime start "t2" s!"waiting 100 before sending {n}"; IO.sleep 100; logWithTime start "t2" s!"sending {n}"; ch2.sync.send n
    logWithTime start "t2" "sending 10"; ch2.sync.send 10
    send 20
    send 30
    send 40
    send 50
    logWithTime start "t2" "waiting 100 before closing channel"; IO.sleep 100; logWithTime start "t2" "closing channel"; ch2.close
    logWithTime start "t2" "closed"

  logWithTime start "main" "runTask1"
  let t1' ← t1.asTask
  logWithTime start "main" "runTask1 started"

  logWithTime start "main" "runTask2"
  let t2' ← t2.asTask
  logWithTime start "main" "runTask2 started"

  logWithTime start "main" "loop start"
  let t3 ← loop 300 ch1 ch2 start
  logWithTime start "main" "loop created"
  let n ← t3.block
  logWithTime start "main" s!"loop finished, received {n}"
  t1'.block
  logWithTime start "main" "t1 finished"
  t2'.block
  logWithTime start "main" "t2 finished"
