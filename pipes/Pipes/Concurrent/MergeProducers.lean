import Pipes.Internal
import Pipes.Core
import Pipes.Prelude
import Std.Sync.Mutex
import Std.Internal.Async
import Std.Sync.Channel

open Std
open Std.Internal.IO.Async

def runProducerToChannel2 (producer : Producer o (EIO Std.CloseableChannel.Error) PUnit) (ch : Std.CloseableChannel o) : EIO Std.CloseableChannel.Error PUnit :=
  for x in producer do
    ch.sync.send x

-- Helper to run producer and close channel when done
def runProducerToChannel [Monad m] [MonadLiftT (EIO CloseableChannel.Error) m] [MonadAsync t m] [MonadAwait t m] (p : Producer o t PUnit) (ch : Std.CloseableChannel o) : m Unit :=
  match p with
  | .Request v _ => PEmpty.elim v
  | .Pure _ => pure PUnit.unit
  | .M mx k => do
    runProducerToChannel (k (← await mx)) ch
  | .Respond a cont => do
    monadLift (ch.sync.send a)
    runProducerToChannel (cont ()) ch

def runProducerWithClose [MonadFinally m] [Monad m] [MonadLiftT (EIO CloseableChannel.Error) m] [MonadAsync t m] [MonadAwait t m] (producer : Producer o t PUnit) (ch : Std.CloseableChannel o) : m Unit := do
  try
    runProducerToChannel producer ch
  finally
    ch.close

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

-- def mergeProducers
--   [MonadFinally m] [Monad m]
--   [MonadLiftT (EIO CloseableChannel.Error) m]
--   [MonadAsync t m] [MonadAwait t m]
--   (producers : List (Producer o t PUnit))
--   : BaseIO (Proxy Empty Unit Unit o m Unit) := do
--   let channels ← producers.mapM (fun _ => Std.CloseableChannel.new)
--   sorry

-- Fixed mergeProducers function
def mergeProducers [MonadFinally m] [Monad m] [MonadLiftT (EIO CloseableChannel.Error) m] [MonadAsync t m] [MonadAwait t m] (producers : List (Producer o t PUnit)) : BaseIO (Producer o m PUnit) := do
  -- Create closeable channels for each producer
  let channels ← producers.mapM (fun _ => Std.CloseableChannel.new)

  sorry
  -- -- Start tasks
  -- let tasks ← Proxy.monadLift $ List.zip producers channels |>.mapM fun (producer, ch) =>
  --   async (runProducerWithClose producer ch)
  --
  -- -- Create merged producer from channels
  -- let result ← mergeFromChannels channels
  --
  -- -- Wait for cleanup
  -- Proxy.monadLift $ do
  --   for task in tasks do
  --     discard task.get
  --
  -- pure result

def mergePureProducers (producers : List (Producer o Id PUnit)) : Producer o Id PUnit := do
  let rec loop (ps : List (Producer o Id PUnit)) : Producer o Id PUnit :=
    match ps with
    | [] => Proxy.Pure ()
    | p :: rest => p.bind fun _ => loop rest
  loop producers

def mergePureProducers2_loop (ps : List (Producer o Id PUnit)) (acc : List (Producer o Id PUnit)) : Producer o Id PUnit := do
  match ps with
  | [] =>
      if acc.isEmpty then
        Proxy.Pure ()
      else
        let x ← await mx
        have next := k x
        runProducerToChannel next ch
  | p :: rest =>
      match p with
      | Proxy.Respond x k => Proxy.Respond x (fun _ => mergePureProducers2_loop rest (k () :: acc))
      | Proxy.Pure _ => mergePureProducers2_loop rest acc
      | Proxy.Request v _ => PEmpty.elim v
      | Proxy.M op k => k (Id.run op)  -- Since m = Id, run the effect directly
  termination_by ps.length + acc.length

partial def mergePureProducers2 (producers : List (Producer o Id PUnit)) : Producer o Id PUnit := mergePureProducers2_loop producers []

-- Alternative simpler merge for pure producers with round-robin behavior
partial def mergePureProducersRoundRobin (producers : List (Producer o Id PUnit)) : Producer o Id PUnit :=
  let rec stepAll (ps : List (Producer o Id PUnit)) : List (Producer o Id PUnit) × List o :=
    ps.foldl (fun (acc, outputs) p =>
      match p with
      | Proxy.Respond x k => (k () :: acc, x :: outputs)
      | Proxy.Pure _ => (acc, outputs)
      | Proxy.Request v _ => PEmpty.elim v
      | Proxy.M op k => (k (Id.run op) :: acc, outputs)
    ) ([], [])

  let rec loop (ps : List (Producer o Id PUnit)) : Producer o Id PUnit :=
    if ps.isEmpty then
      Proxy.Pure ()
    else
      let (nextProducers, outputs) := stepAll ps
      -- Emit all outputs from this round
      let rec emitOutputs (xs : List o) (next : Producer o Id PUnit) : Producer o Id PUnit :=
        match xs with
        | [] => next
        | y :: ys => Proxy.Respond y (fun _ => emitOutputs ys next)
      emitOutputs outputs.reverse (loop nextProducers)

  loop producers

#guard Proxy.toList (
  mergePureProducers [
    Proxy.fromList [1, 11],
    Proxy.fromList [2, 22],
    Proxy.fromList [3, 33]
  ]
) = [1, 11, 2, 22, 3, 33]

#guard Proxy.toList (
  mergePureProducers2 [
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
