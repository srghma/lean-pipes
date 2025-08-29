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

import Pipes.Internal
import Pipes.Core
import Pipes.Prelude
import Std.Sync.Mutex
import Std.Sync.Channel
import Std.Internal.Async.Basic
import Std.Internal.Async.Select

partial def Producer.Unbounded.fromCloseableChannel [MonadLiftT BaseIO m] (ch : Std.CloseableChannel α) : Producer α m PUnit :=
  Proxy.M (monadLift ch.sync.recv) fun
    | some a => Proxy.Respond a (fun _ => Producer.Unbounded.fromCloseableChannel ch)
    | none   => Proxy.Pure ()

-- (fun x => IO (Std.Internal.IO.Async.AsyncTask x))
open Std.Internal.IO.Async in
partial def Producer.Unbounded.fromCloseableChannels (chs : Array (Std.CloseableChannel α)) : Producer α (fun x => IO (AsyncTask x)) PUnit :=
  if chs.isEmpty then
    Proxy.Pure ()
  else
    Proxy.M (Selectable.one $
      chs.mapIdx fun i ch =>
        Selectable.case ch.recvSelector fun (data : Option α) =>
          return AsyncTask.pure (data, if data.isSome then chs else chs.eraseIdx! i)
    ) fun ((mvalue, chs') : Option α × Array (Std.CloseableChannel α)) =>
      match mvalue with
      | some value => Proxy.Respond value fun _ => fromCloseableChannels chs'
      | none => fromCloseableChannels chs'


-- private def selectFromChannelsTuplesTask
--   (chsAndTasks : List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit)))
--   : BaseIO (Option (o × List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit)))) := do
--   let rec go (acc : List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit)))
--              (rest : List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit))) : BaseIO _ :=
--     match rest with
--     | [] => return none
--     | (ch, t) :: xs => do
--       match ← ch.sync.recv with
--       | some v => return some (v, acc ++ xs ++ [(ch, t)])
--       | none   => go (acc ++ [(ch, t)]) xs
--   go [] chsAndTasks

private partial def mergeProducers.loopTask
  [MonadFinally m] [Monad m]
  [MonadLiftT BaseIO m]
  [MonadLiftT (EIO Std.CloseableChannel.Error) m]
  (chsAndTasks : List (Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit)))
  : Producer o m PUnit := sorry
--   match chsAndTasks with
--   | [] => Proxy.Pure ()
--   | _ =>
--     Proxy.M (monadLift $ selectFromChannelsTuplesTask chsAndTasks) fun
--       | some (v, rest) => Proxy.Respond v (fun _ => mergeProducers.loopTask rest)
--       | none =>
--         -- wait for all workers to finish (ignore results)
--         Proxy.M (monadLift $ do
--           let mut results : List (Except Std.CloseableChannel.Error Unit) := []
--           for (_, t) in chsAndTasks do
--             let r ← IO.wait t
--             results := results ++ [r]
--           pure results
--         ) fun _ =>
--           Proxy.Pure ()

def mergeProducers.runProducerToChannel [Monad m] [MonadLiftT (EIO Std.CloseableChannel.Error) m] [MonadLiftT BaseIO m] (p : Producer o BaseIO PUnit) (ch : Std.CloseableChannel o) : m Unit :=
  match p with
  | .Request v _ => PEmpty.elim v
  | .Pure _ => closeIfNotClosed ch
  | .M mx k => unlessImACanceledTask ch do runProducerToChannel (k (← mx)) ch
  | .Respond a cont => unlessImACanceledTask ch do ch.sync.send a; runProducerToChannel (cont ()) ch
  where
    closeIfNotClosed (ch : Std.CloseableChannel o): m Unit := do if ← ch.isClosed then return else ch.close
    unlessImACanceledTask (ch : Std.CloseableChannel o) (t : m Unit) : m Unit := do if ← IO.checkCanceled then closeIfNotClosed ch else t

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
        let t ← EIO.asTask (mergeProducers.runProducerToChannel producer ch) -- unwraps a producer like an onion, when nothing - stops channel, TODO: also we should remove this producer from list of producers from a next round
        pure (ch, t)
    pure chsAndTasks
  ) mergeProducers.loopTask

-- open Std.Internal.IO.Async in
-- def Producer.selector (prod : Producer b BaseIO PUnit) : Selector b := {
--   tryFn := do
--     match prod with
--     | .Respond b k => return some b
--     | .Pure _ => return none
--     | .M op k => do
--       let x ← op
--       let next := k x
--       -- Recursively try the next step, but avoid infinite loops by limiting recursion depth
--       if (← IO.getNumHeartbeats) < 1000 then
--         selector next |>.tryFn
--       else
--         return none
--     | .Request v _ => PEmpty.elim v
--
--   registerFn := fun waiter => do
--     let task := IO.asTask do
--       match prod with
--       | .Respond b k => do
--         let lose := return ()
--         let win promise := do
--           promise.resolve (.ok b)
--         if ← waiter.race lose win then
--           -- If we won, continue with the next producer state
--           let nextProd := k ()
--           -- Register again for the next value
--           selector nextProd |>.registerFn waiter
--       | .Pure _ => do
--         let lose := return ()
--         let win promise := promise.resolve (.error <| IO.Error.userError "Producer terminated")
--         discard <| waiter.race lose win
--       | .M op k => do
--         let x ← op
--         let next := k x
--         selector next |>.registerFn waiter
--       | .Request v _ => PEmpty.elim v
--     -- Store the task in the waiter for cancellation
--     waiter.finished.setTask task
--
--   unregisterFn := do
--     -- Cancel the task if it exists
--     match ← waiter.finished.getTask with
--     | some task => IO.cancel task
--     | none => return ()
-- }
