import Std.Sync.Channel
import Std.Internal.Async
import Pipes.Concurrent.MergeProducers

def logWithTime (start : Nat) (tag msg : String) : IO Unit := do
  let now ← IO.monoMsNow
  let elapsed := now - start
  IO.println s!"[+{elapsed}ms][{tag}] {msg}"

partial def readAllFromChannel.impl [ToString α] (start : Nat) (ch : Std.CloseableChannel α) (acc : List α) : IO (List α) := do
  match ← ch.sync.recv with
  | some x => do
    logWithTime start "main" s!"ch.sync.recv is some {x}"
    impl start ch (x :: acc)
  | none => do
    logWithTime start "main" s!"ch.sync.recv is none"
    return acc

def readAllFromChannel [ToString α] (start : Nat) (ch : Std.CloseableChannel α) : IO (List α) :=
  return (← readAllFromChannel.impl start ch []).reverse

-- Test individual components first
def testRunProducerToChannel (start : Nat) : IO (List Nat) := do
  let ch ← Std.CloseableChannel.new
  let producer : Producer Nat BaseIO PUnit := do
    Proxy.yield 1
    Proxy.yield 2
    Proxy.yield 3

  let task ← EIO.asTask (
    try
      runProducerToChannel 9999 producer ch
    finally
      ch.close
    )
  let results ← readAllFromChannel start ch
  monadLift $ EIO.ofExcept $ ← IO.wait task
  return results

def main : IO Unit := do
  let start ← IO.monoMsNow -- reference time
  let r <- testRunProducerToChannel start
  logWithTime start "main" s!"result is {r}"
