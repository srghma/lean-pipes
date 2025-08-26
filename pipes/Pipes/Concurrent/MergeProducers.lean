import Pipes.Internal
import Pipes.Core
import Pipes.Prelude
import Std.Sync.Mutex
import Std.Sync.Channel

-- def runProducerToChannel_using_for (producer : Producer o (EIO Std.CloseableChannel.Error) PUnit) (ch : Std.CloseableChannel o) : EIO Std.CloseableChannel.Error PUnit :=
--   for x in producer do
--     ch.sync.send x

-- def runProducerToChannelTask (p : Producer o Task PUnit) (ch : Std.CloseableChannel o) : EIO Std.CloseableChannel.Error Unit :=
--   match p with
--   | .Request v _ => PEmpty.elim v
--   | .Pure _      => pure ()
--   | .M t k       => do
--     let x ← IO.wait t   -- wait for the task in BaseIO
--     runProducerToChannelTask (k x) ch
--   | .Respond a cont => do
--     ch.sync.send a
--     runProducerToChannelTask (cont ()) ch
--
-- def runProducerWithClose [MonadFinally m] [Monad m] [MonadLiftT BaseIO m] [MonadLiftT (EIO Std.CloseableChannel.Error) m] (producer : Producer o Task PUnit) (ch : Std.CloseableChannel o) : m Unit := do
--   try
--     runProducerToChannelTask producer ch
--   finally
--     monadLift (ch.close)

partial def CloseableChannel.Unbounded.toProducer [MonadLiftT BaseIO m] (ch : Std.CloseableChannel α) : Producer α m PUnit :=
  Proxy.M (monadLift ch.sync.recv) fun
    | some a => Proxy.Respond a (fun _ => CloseableChannel.Unbounded.toProducer ch)
    | none   => Proxy.Pure ()

-- def selectFromChannels (channels : List (Std.CloseableChannel α)) : BaseIO (Option (α × List (Std.CloseableChannel α))) := do
--   -- This is a simplified version - in practice you'd want proper channel selection
--   for ch in channels do
--     match ← ch.sync.recv with
--     | some value => return some (value, channels)
--     | none => continue
--   return none

-- partial def mergeFromChannels (chs : List (Std.CloseableChannel o)) : Producer o BaseIO PUnit :=
--   if chs.isEmpty then
--     Proxy.Pure ()
--   else
--     Proxy.M (monadLift $ selectFromChannels chs) fun
--       | some (value, remainingChannels) =>
--           Proxy.Respond value (fun _ => mergeFromChannels remainingChannels)
--       | none =>
--           Proxy.Pure ()

-- def selectFromChannelsTuples (chsAndTasks : List (Std.CloseableChannel o × Task PUnit)) : BaseIO (Option (o × List (Std.CloseableChannel o × Task PUnit))) := do
--   let rec go (acc : List (Std.CloseableChannel o × Task PUnit)) (rest : List (Std.CloseableChannel o × Task PUnit)) : BaseIO (Option (o × List (Std.CloseableChannel o × Task PUnit))) :=
--     match rest with
--     | [] => return none
--     | (ch, t) :: xs => do
--       let x ← ch.sync.recv
--       match x with
--       | some value => return some (value, acc ++ xs ++ [(ch, t)]) -- put remaining tuples back
--       | none => go (acc ++ [(ch, t)]) xs
--   go [] chsAndTasks

-- private partial def mergeProducers.loop
--   [MonadFinally m] [Monad m]
--   [MonadLiftT BaseIO m]
--   [MonadLiftT (EIO Std.CloseableChannel.Error) m]
--   (chsAndTasks : List (Std.CloseableChannel o × Task PUnit)) : Producer o m PUnit :=
--   match chsAndTasks with
--   | [] => Proxy.Pure ()
--   | _ => Proxy.M (monadLift $ selectFromChannelsTuples chsAndTasks) fun
--     | some (v, remainingTuples) => Proxy.Respond v (fun _ => mergeProducers.loop remainingTuples)
--     | none => Proxy.M (monadLift $ chsAndTasks.forM fun (_, t) => IO.wait t) fun _ => Proxy.Pure ()

def runProducerToChannel [Monad m] [MonadLiftT (EIO Std.CloseableChannel.Error) m] [MonadLiftT BaseIO m] (p : Producer o BaseIO PUnit) (ch : Std.CloseableChannel o) : m Unit :=
  match p with
  | .Request v _ => PEmpty.elim v
  | .Pure _ => pure PUnit.unit
  | .M mx k => do
    let x ← monadLift mx
    runProducerToChannel (k x) ch
  | .Respond a cont => do
    monadLift (ch.sync.send a)
    runProducerToChannel (cont ()) ch

private def selectFromChannelsTuplesTask
  (chsAndTasks : List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit)))
  : BaseIO (Option (o × List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit)))) := do
  let rec go (acc : List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit)))
             (rest : List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit))) : BaseIO _ :=
    match rest with
    | [] => return none
    | (ch, t) :: xs => do
      match ← ch.sync.recv with
      | some v => return some (v, acc ++ xs ++ [(ch, t)])
      | none   => go (acc ++ [(ch, t)]) xs
  go [] chsAndTasks

private partial def mergeProducers.loopTask
  [MonadFinally m] [Monad m]
  [MonadLiftT BaseIO m]
  [MonadLiftT (EIO Std.CloseableChannel.Error) m]
  (chsAndTasks : List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit)))
  : Producer o m PUnit :=
  match chsAndTasks with
  | [] => Proxy.Pure ()
  | _ =>
    Proxy.M (monadLift $ selectFromChannelsTuplesTask chsAndTasks) fun
      | some (v, rest) => Proxy.Respond v (fun _ => mergeProducers.loopTask rest)
      | none =>
        -- wait for all workers to finish (ignore results)
        Proxy.M (monadLift $ do
          let mut results : List (Except Std.CloseableChannel.Error Unit) := []
          for (_, t) in chsAndTasks do
            let r ← IO.wait t
            results := results ++ [r]
          pure results
        ) fun _ =>
          Proxy.Pure ()

def mergeProducers
  [MonadFinally m] [Monad m]
  [MonadLiftT BaseIO m]
  [MonadLiftT (EIO Std.CloseableChannel.Error) m]
  (producers : List (Producer o BaseIO PUnit))
  : Producer o m PUnit :=
  Proxy.M (do
    let chsAndTasks ← monadLift $ do
      producers.mapM fun (producer) => do
        let ch <- Std.CloseableChannel.new
        let t ← EIO.asTask (
          try
            -- pick m := EIO CloseableChannel.Error for the generic runner
            runProducerToChannel producer ch
          finally
            ch.close
        )
        pure (ch, t)
    pure chsAndTasks
  ) mergeProducers.loopTask
