import Std.Sync.Channel
import Std.Internal.Async
import Pipes.Concurrent.MergeProducers

def logWithTime (start : Nat) (tag msg : String) : BaseIO Unit := do
  let now ← IO.monoMsNow
  let elapsed := now - start
  dbg_trace s!"[+{elapsed}ms][{tag}] {msg}"

def testMergeProducersIntegration (start : Nat) : EIO MergeError (List Nat) := do
  let producers : Array (Producer Nat BaseIO PUnit) := #[
    do
      Proxy.monadLift (logWithTime start "p1" "yielding 1")
      Proxy.yield 1
      Proxy.monadLift (logWithTime start "p1" "yielding 11")
      Proxy.yield 11
      Proxy.monadLift (logWithTime start "p1" "ended"),
    do
      Proxy.monadLift (logWithTime start "p2" "yielding 2")
      Proxy.yield 2
      Proxy.monadLift (logWithTime start "p2" "yielding 22")
      Proxy.yield 22,
      Proxy.monadLift (logWithTime start "p2" "ended"),
    do
      Proxy.monadLift (logWithTime start "p3" "yielding 3")
      Proxy.yield 3
      Proxy.monadLift (logWithTime start "p3" "yielding 33")
      Proxy.yield 33
      Proxy.monadLift (logWithTime start "p3" "ended")
  ]

  -- Merge them and collect results, logging each receive
  let merged := mergeProducers producers

  (·.2) <$> Proxy.toListM merged

def main : IO Unit := do
  let start ← IO.monoMsNow -- reference time
  let r <- testMergeProducersIntegration start
  logWithTime start "main" s!"result is {r}"
