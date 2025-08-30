import Pipes.Concurrent.MergeProducers
import Std.Sync.Mutex
import Std.Sync.Channel

-- Test functions for mergeProducers

-- First, let's create some simple test producers that work with BaseIO
def testProducer1 : Producer Nat BaseIO PUnit := do
  Proxy.yield 1
  Proxy.yield 11

def testProducer2 : Producer Nat BaseIO PUnit := do
  Proxy.yield 2
  Proxy.yield 22

def testProducer3 : Producer Nat BaseIO PUnit := do
  Proxy.yield 3
  Proxy.yield 33

-- Test the mergeProducers function
def testMergeProducers : EIO MergeError (Unit × List Nat) := do
  let merged := mergeProducers #[testProducer1, testProducer2, testProducer3]
  Proxy.toListM merged

-- A simpler test that doesn't require full concurrent execution
-- Let's create a version that works with EIO and test it step by step

-- Test individual components first
def testRunProducerToChannel : EIO Std.CloseableChannel.Error (List Nat) := do
  let ch ← Std.CloseableChannel.new
  let producer : Producer Nat BaseIO PUnit := do
    Proxy.yield 1
    Proxy.yield 2
    Proxy.yield 3

  -- Run producer in a task
  let task ← EIO.asTask (
    try
      runProducerToChannel producer ch
    finally
      ch.close
  )

  -- Read from channel until empty
  let mut results : List Nat := []
  repeat
    match ← ch.sync.recv with
    | some x => results := results ++ [x]
    | none => break

  -- Wait for task to complete
  let _ ← IO.wait task

  return results

-- Test channel-to-producer conversion
-- def testChannelToProducer : EIO Std.CloseableChannel.Error (Except MergeError Unit × List Nat) := do
def testChannelToProducer : EIO Std.CloseableChannel.Error (List Nat) := do
  let ch ← Std.CloseableChannel.new

  -- Send some data to the channel
  ch.sync.send 1
  ch.sync.send 2
  ch.sync.send 3
  ch.close

  -- Convert channel to producer and collect results
  let producer := (Producer.Unbounded.fromCloseableChannel ch : Producer Nat BaseIO PUnit)
  let (.unit, x) ← monadLift $ Proxy.toListM producer
  return x

-- Integration test for the full mergeProducers pipeline
def testMergeProducersIntegration : EIO MergeError (List Nat) := do
  -- Create some simple producers
  let producers : Array (Producer Nat BaseIO PUnit) := #[
    do Proxy.yield 1; Proxy.yield 11,
    do Proxy.yield 2; Proxy.yield 22,
    do Proxy.yield 3; Proxy.yield 33
  ]
  let (.unit, x) ← monadLift $ Proxy.toListM $ mergeProducers producers
  return x

-- Test runners
#eval do -- [1, 2, 3]
  let result ← monadLift testRunProducerToChannel
  IO.println s!"testRunProducerToChannel: {result}"

#eval do -- [1, 2, 3]
  let result ← monadLift testChannelToProducer
  IO.println s!"testChannelToProducer: {result}"

#eval do -- [1]
  let result ← monadLift testMergeProducersIntegration
  IO.println s!"testMergeProducersIntegration: {result}"

-- Performance/stress test with more producers
def testMergeProducersStress : EIO MergeError (List Nat) := do
  let producers := Array.range 10 |>.map fun i =>
    (do Proxy.yield i; Proxy.yield (i + 100) : Producer Nat BaseIO PUnit)

  let (.unit, x) ← monadLift $ Proxy.toListM $ mergeProducers producers
  return x

#eval do -- [0, 7] or [1, 9] or [8] or [0, 3] --
  let result ← monadLift testMergeProducersStress
  IO.println s!"testMergeProducersStress: {result}"
