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
  let producer : Producer Nat BaseIO Unit := do
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
  let (_ : Option Unit) <- monadLift $ EIO.ofExcept $ ← IO.wait task
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

/-- info: #[1, 2, 3, 11, 22, 33] -/
#guard_msgs in #eval return (← testMergeProducersIntegration).toArray.qsort

-- Performance/stress test with more producers
def testMergeProducersStress : EIO MergeError (List Nat) := do
  let producers := Array.range 10 |>.map fun i =>
    (do
      -- dbg_trace s!"[producer {i}] yielding {i}"
      Proxy.yield i
      -- dbg_trace s!"[producer {i}] yielding {i+100}"
      (Proxy.yield (i + 100) : Producer Nat BaseIO PUnit)
      -- dbg_trace s!"[producer {i}] yielding finish"
      )
  (·.2) <$> (monadLift $ Proxy.toListM $ mergeProducers producers)

/-- info: #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109] -/
#guard_msgs in #eval return (← testMergeProducersStress).toArray.qsort
