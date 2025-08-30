import Pipes.Concurrent.MergeProducers

partial def readAllFromChannel.impl (ch : Std.CloseableChannel α) (acc : List α) : IO (List α) := do
  match ← ch.sync.recv with
  | some x => do impl ch (x :: acc)
  | none => do return acc

def readAllFromChannel (ch : Std.CloseableChannel α) : IO (List α) :=
  return (← readAllFromChannel.impl ch []).reverse

-- Test individual components first
def testRunProducerToChannel : IO (List Nat) := do
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
  let results ← readAllFromChannel ch
  monadLift $ EIO.ofExcept $ ← IO.wait task
  return results

/-- info: [1, 2, 3] -/
#guard_msgs in #eval do IO.println (← monadLift testRunProducerToChannel)

def testChannelToProducer : EIO Std.CloseableChannel.Error (List Nat) := do
  let ch ← Std.CloseableChannel.new

  -- Send some data to the channel
  ch.sync.send 1
  ch.sync.send 2
  ch.sync.send 3
  ch.close

  -- Convert channel to producer and collect results
  let producer := (Producer.Unbounded.fromCloseableChannel ch : Producer Nat BaseIO PUnit)
  (·.2) <$> (monadLift $ Proxy.toListM producer)

/-- info: [1, 2, 3] -/
#guard_msgs in #eval do IO.println (← monadLift testChannelToProducer)

-- Integration test for the full mergeProducers pipeline
def testMergeProducersIntegration : EIO MergeError (List Nat) := do
  -- Create some simple producers
  let producers : Array (Producer Nat BaseIO PUnit) := #[
    do Proxy.yield 1; Proxy.yield 11,
    do Proxy.yield 2; Proxy.yield 22,
    do Proxy.yield 3; Proxy.yield 33
  ]
  (·.2) <$> (monadLift $ Proxy.toListM $ mergeProducers producers)

#eval do -- [1] or [2,3] or [1,3] or [2, 3, 33, 1]
  let result ← monadLift testMergeProducersIntegration
  IO.println s!"testMergeProducersIntegration: {result}"

-- Performance/stress test with more producers
def testMergeProducersStress : EIO MergeError (List Nat) := do
  let producers := Array.range 10 |>.map fun i =>
    (do
      dbg_trace s!"[producer {i}] yielding {i}"
      Proxy.yield i
      dbg_trace s!"[producer {i}] yielding {i+100}"
      (Proxy.yield (i + 100) : Producer Nat BaseIO PUnit)
      dbg_trace s!"[producer {i}] yielding finish")
  (·.2) <$> (monadLift $ Proxy.toListM $ mergeProducers producers)

#eval do -- [0, 7] or [1, 9] or [8] or [0, 3] --
  let result ← monadLift testMergeProducersStress
  IO.println s!"testMergeProducersStress: {result}"
