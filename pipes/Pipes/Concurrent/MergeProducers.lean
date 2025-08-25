import Pipes.Internal
import Pipes.Core
import Pipes.Prelude
import Std.Sync.Mutex
-- import Std.Internal.Async
import Std.Sync.Channel
import Aesop

open Std
-- open Std.Internal.IO.Async

def runProducerToChannel2 (producer : Producer o (EIO Std.CloseableChannel.Error) PUnit) (ch : Std.CloseableChannel o) : EIO Std.CloseableChannel.Error PUnit :=
  for x in producer do
    ch.sync.send x

-- Helper to run producer and close channel when done
def runProducerToChannel [Monad m] [MonadLiftT (EIO CloseableChannel.Error) m] [MonadLiftT BaseIO m] (p : Producer o BaseIO PUnit) (ch : Std.CloseableChannel o) : m Unit :=
  match p with
  | .Request v _ => PEmpty.elim v
  | .Pure _ => pure PUnit.unit
  | .M mx k => do
    let x ← monadLift mx
    runProducerToChannel (k x) ch
  | .Respond a cont => do
    monadLift (ch.sync.send a)
    runProducerToChannel (cont ()) ch

def runProducerToChannelTask (p : Producer o Task PUnit) (ch : Std.CloseableChannel o) : EIO CloseableChannel.Error Unit :=
  match p with
  | .Request v _ => PEmpty.elim v
  | .Pure _      => pure ()
  | .M t k       => do
    let x ← IO.wait t   -- wait for the task in BaseIO
    runProducerToChannelTask (k x) ch
  | .Respond a cont => do
    ch.sync.send a
    runProducerToChannelTask (cont ()) ch

def runProducerWithClose [MonadFinally m] [Monad m] [MonadLiftT BaseIO m] [MonadLiftT (EIO CloseableChannel.Error) m] (producer : Producer o Task PUnit) (ch : Std.CloseableChannel o) : m Unit := do
  try
    runProducerToChannelTask producer ch
  finally
    monadLift (ch.close)

partial def CloseableChannel.Unbounded.toProducer [MonadLiftT BaseIO m] (ch : CloseableChannel α) : Producer α m PUnit :=
  Proxy.M (monadLift ch.sync.recv) fun
    | some a => Proxy.Respond a (fun _ => CloseableChannel.Unbounded.toProducer ch)
    | none   => Proxy.Pure ()

-- Helper function to select from multiple channels
def selectFromChannels (channels : List (CloseableChannel α)) : BaseIO (Option (α × List (CloseableChannel α))) := do
  -- This is a simplified version - in practice you'd want proper channel selection
  for ch in channels do
    match ← ch.sync.recv with
    | some value => return some (value, channels)
    | none => continue
  return none

partial def mergeFromChannels (chs : List (CloseableChannel o)) : Producer o BaseIO PUnit :=
  if chs.isEmpty then
    Proxy.Pure ()
  else
    Proxy.M (monadLift $ selectFromChannels chs) fun
      | some (value, remainingChannels) =>
          Proxy.Respond value (fun _ => mergeFromChannels remainingChannels)
      | none =>
          Proxy.Pure ()

def selectFromChannelsTuples (chsAndTasks : List (CloseableChannel o × Task PUnit)) : BaseIO (Option (o × List (CloseableChannel o × Task PUnit))) := do
  let rec go (acc : List (CloseableChannel o × Task PUnit)) (rest : List (CloseableChannel o × Task PUnit)) : BaseIO (Option (o × List (CloseableChannel o × Task PUnit))) :=
    match rest with
    | [] => return none
    | (ch, t) :: xs => do
      let x ← ch.sync.recv
      match x with
      | some value => return some (value, acc ++ xs ++ [(ch, t)]) -- put remaining tuples back
      | none => go (acc ++ [(ch, t)]) xs
  go [] chsAndTasks

partial def mergeProducers.loop
  [MonadFinally m] [Monad m]
  [MonadLiftT BaseIO m]
  [MonadLiftT (EIO CloseableChannel.Error) m]
  (chsAndTasks : List (CloseableChannel o × Task PUnit)) : Producer o m PUnit :=
  match chsAndTasks with
  | [] => Proxy.Pure ()
  | _ =>
    Proxy.M (monadLift $ selectFromChannelsTuples chsAndTasks) fun
      | some (v, remainingTuples) =>
          Proxy.Respond v (fun _ => mergeProducers.loop remainingTuples)
      | none =>
          -- All channels empty, wait for tasks to finish
          Proxy.M (monadLift $ chsAndTasks.forM fun (_, t) => IO.wait t) fun _ =>
            Proxy.Pure ()


def runProducerWithCloseE
  (producer : Producer o BaseIO PUnit)
  (ch : Std.CloseableChannel o)
  : EIO CloseableChannel.Error Unit := do
  try
    -- pick m := EIO CloseableChannel.Error for the generic runner
    runProducerToChannel (m := EIO CloseableChannel.Error) producer ch
  finally
    ch.close

def selectFromChannelsTuplesTask
  (chsAndTasks : List (CloseableChannel o × Task (Except CloseableChannel.Error Unit)))
  : BaseIO (Option (o × List (CloseableChannel o × Task (Except CloseableChannel.Error Unit)))) := do
  let rec go (acc : List (CloseableChannel o × Task (Except CloseableChannel.Error Unit)))
             (rest : List (CloseableChannel o × Task (Except CloseableChannel.Error Unit))) : BaseIO _ :=
    match rest with
    | [] => return none
    | (ch, t) :: xs => do
      match ← ch.sync.recv with
      | some v => return some (v, acc ++ xs ++ [(ch, t)])
      | none   => go (acc ++ [(ch, t)]) xs
  go [] chsAndTasks

partial def mergeProducers.loopTask
  [MonadFinally m] [Monad m]
  [MonadLiftT BaseIO m]
  [MonadLiftT (EIO CloseableChannel.Error) m]
  (chsAndTasks : List (CloseableChannel o × Task (Except CloseableChannel.Error Unit)))
  : Producer o m PUnit :=
  match chsAndTasks with
  | [] => Proxy.Pure ()
  | _ =>
    Proxy.M (monadLift $ selectFromChannelsTuplesTask chsAndTasks) fun
      | some (v, rest) =>
          Proxy.Respond v (fun _ => mergeProducers.loopTask rest)
      | none =>
          -- wait for all workers to finish (ignore results)
          Proxy.M (monadLift $ do
            -- chsAndTasks : List (CloseableChannel o × Task (Except CloseableChannel.Error Unit))
            let mut results : List (Except CloseableChannel.Error Unit) := []
            for (_, t) in chsAndTasks do
              let r ← IO.wait t              -- BaseIO (Except ... Unit)
              results := results ++ [r]
            pure results
          ) fun _ =>
            Proxy.Pure ()

def mergeProducers
  [MonadFinally m] [Monad m]
  [MonadLiftT BaseIO m]
  [MonadLiftT (EIO CloseableChannel.Error) m]
  (producers : List (Producer o BaseIO PUnit))
  : Producer o m PUnit :=
  Proxy.M (do
    let chsAndTasks ← monadLift $ do
      producers.mapM fun (producer) => do
        let ch <- Std.CloseableChannel.new
        let t ← EIO.asTask (runProducerWithCloseE producer ch)
        pure (ch, t)
    pure chsAndTasks
  ) mergeProducers.loopTask

def mergePureProducersConcat (producers : List (Producer o Id PUnit)) : Producer o Id PUnit := do
  match producers with
  | [] => Proxy.Pure ()
  | p :: rest => p.bind fun _ => mergePureProducersConcat rest

partial def mergePureProducersTwoPhase_loop (ps : List (Producer o Id PUnit)) (acc : List (Producer o Id PUnit)) : Producer o Id PUnit := do
  match ps with
  | [] =>
      if acc.isEmpty then
        Proxy.Pure ()
      else
        mergePureProducersTwoPhase_loop (acc.reverse) []
  | p :: rest =>
      match p with
      | Proxy.Respond x k => Proxy.Respond x (fun _ => mergePureProducersTwoPhase_loop rest (k () :: acc))
      | Proxy.Pure _ => mergePureProducersTwoPhase_loop rest acc
      | Proxy.Request v _ => PEmpty.elim v
      | Proxy.M op k => k (Id.run op)  -- Since m = Id, run the effect directly
  -- termination_by ps.length + acc.length
  -- decreasing_by
  --   sorry

partial def mergePureProducersTwoPhase (producers : List (Producer o Id PUnit)) : Producer o Id PUnit := mergePureProducersTwoPhase_loop producers []

def mergePureProducersRoundRobin_stepAll (ps : List (Producer o Id PUnit)) : List (Producer o Id PUnit) × List o :=
  ps.foldl (fun (acc, outputs) p =>
    match p with
    | Proxy.Respond x k => (k () :: acc, x :: outputs)
    | Proxy.Pure _ => (acc, outputs)
    | Proxy.Request v _ => PEmpty.elim v
    | Proxy.M op k => (k (Id.run op) :: acc, outputs)
  ) ([], [])

def mergePureProducersRoundRobin_emitOutputs (xs : List o) (next : Producer o Id PUnit) : Producer o Id PUnit :=
  match xs with
  | [] => next
  | y :: ys => Proxy.Respond y (fun _ => mergePureProducersRoundRobin_emitOutputs ys next)

partial def mergePureProducersRoundRobin (ps : List (Producer o Id PUnit)) : Producer o Id PUnit :=
  match ps with
  | [] => Proxy.Pure ()
  | x :: rest =>
      let (nextProducers, outputs) := mergePureProducersRoundRobin_stepAll (x :: rest)
      -- have h : nextProducers.length ≤ ps.length := by
      --   sorry
      mergePureProducersRoundRobin_emitOutputs outputs.reverse (mergePureProducersRoundRobin nextProducers)

#guard Proxy.toList (
  mergePureProducersConcat [
    Proxy.fromList [1, 11],
    Proxy.fromList [2, 22],
    Proxy.fromList [3, 33]
  ]
) = [1, 11, 2, 22, 3, 33]

#guard Proxy.toList (
  mergePureProducersTwoPhase [
    Proxy.fromList [1, 11],
    Proxy.fromList [2, 22],
    Proxy.fromList [3, 33]
  ]
) = [1, 2, 3, 11, 22, 33]

#guard Proxy.toList (
  mergePureProducersRoundRobin [
    Proxy.fromList [1, 11],
    Proxy.fromList [2, 22],
    Proxy.fromList [3, 33]
  ]
) = [1, 2, 3, 33, 22, 11]

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
def testMergeProducers : EIO CloseableChannel.Error (List Nat) := do
  let merged := mergeProducers [testProducer1, testProducer2, testProducer3]
  Proxy.toListM merged

-- A simpler test that doesn't require full concurrent execution
-- Let's create a version that works with EIO and test it step by step

-- Test individual components first
def testRunProducerToChannel : EIO CloseableChannel.Error (List Nat) := do
  let ch ← CloseableChannel.new
  let producer : Producer Nat BaseIO PUnit := do
    Proxy.yield 1
    Proxy.yield 2
    Proxy.yield 3

  -- Run producer in a task
  let task ← EIO.asTask (runProducerWithCloseE producer ch)

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
def testChannelToProducer : EIO CloseableChannel.Error (List Nat) := do
  let ch ← CloseableChannel.new

  -- Send some data to the channel
  ch.sync.send 1
  ch.sync.send 2
  ch.sync.send 3
  ch.close

  -- Convert channel to producer and collect results
  let producer := CloseableChannel.Unbounded.toProducer ch
  Proxy.toListM producer

-- Integration test for the full mergeProducers pipeline
def testMergeProducersIntegration : EIO CloseableChannel.Error (List Nat) := do
  -- Create some simple producers
  let producers : List (Producer Nat BaseIO PUnit) := [
    do Proxy.yield 1; Proxy.yield 11,
    do Proxy.yield 2; Proxy.yield 22,
    do Proxy.yield 3; Proxy.yield 33
  ]

  -- Use mergeProducers to combine them
  let merged := mergeProducers (m := EIO CloseableChannel.Error) producers

  -- Collect all results
  Proxy.toListM merged

-- Test runners
#eval do
  let result ← monadLift testRunProducerToChannel
  IO.println s!"testRunProducerToChannel: {result}"

#eval do
  let result ← monadLift testChannelToProducer
  IO.println s!"testChannelToProducer: {result}"

#eval do
  let result ← monadLift testMergeProducersIntegration
  IO.println s!"testMergeProducersIntegration: {result}"

-- Performance/stress test with more producers
def testMergeProducersStress : EIO CloseableChannel.Error (List Nat) := do
  let producers := List.range 10 |>.map fun i =>
    (do Proxy.yield i; Proxy.yield (i + 100) : Producer Nat BaseIO PUnit)

  let merged := mergeProducers (m := EIO CloseableChannel.Error) producers
  Proxy.toListM merged

#eval do
  let result ← monadLift testMergeProducersStress
  IO.println s!"testMergeProducersStress: {result}"
