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

import Pipes.Internal
import Pipes.Core
import Pipes.Prelude
import Std.Sync.Mutex
import Std.Sync.Channel
import Std.Internal.Async.Basic
import Std.Internal.Async.Select
import Init.System.IO
import Aesop

partial def Producer.Unbounded.fromCloseableChannel [MonadLiftT BaseIO m] (ch : Std.CloseableChannel α) : Producer α m PUnit :=
  Proxy.M (monadLift ch.sync.recv) fun
    | some a => Proxy.Respond a (fun _ => Producer.Unbounded.fromCloseableChannel ch)
    | none   => Proxy.Pure ()

partial def Producer.Unbounded.fromCloseableChannels (chs : Array (Std.CloseableChannel α)) : Producer α (fun x => IO (Std.Internal.IO.Async.AsyncTask x)) PUnit :=
  if chs.isEmpty then
    Proxy.Pure ()
  else
    Proxy.M (Std.Internal.IO.Async.Selectable.one $
      chs.mapIdx fun i ch =>
        Std.Internal.IO.Async.Selectable.case ch.recvSelector fun (data : Option α) =>
          return Std.Internal.IO.Async.AsyncTask.pure (data, if data.isSome then chs else chs.eraseIdx! i)
    ) fun ((mvalue, chs') : Option α × Array (Std.CloseableChannel α)) =>
      match mvalue with
      | some value => Proxy.Respond value fun _ => fromCloseableChannels chs'
      | none => fromCloseableChannels chs'


attribute [-instance] Std.CloseableChannel.instMonadLiftEIOErrorIO

/--
I just send, I dont close channel (even if my thread was canceled), user should do this,
I can only fail in `send` if channel was closed but I tried to send value (which should not happen really)
-/
def runProducerToChannel
  -- [ToString o]
  -- [Monad m]
  -- [MonadLift m (EIO Std.CloseableChannel.Error)]
  (prodIdx : Nat)
  (p : Producer o BaseIO PUnit)
  (ch : Std.CloseableChannel o) :
  EIO Std.CloseableChannel.Error Unit :=
  match p with
  | .Request v _ => PEmpty.elim v
  | .Pure _ => do
    -- dbg_trace s!"[producer to channel ({prodIdx})] return .unit"
    return .unit
  | .M mx k => unlessImACanceledDo do
    runProducerToChannel prodIdx (k (← mx)) ch
  | .Respond a cont => unlessImACanceledDo do
    -- dbg_trace s!"[producer to channel ({prodIdx})] sending {a}"
    let task ← Std.CloseableChannel.send ch a
    EIO.ofExcept $ ← IO.wait task
    -- dbg_trace s!"[producer to channel ({prodIdx})]   sending res is ok {a}"
    runProducerToChannel prodIdx (cont ()) ch
  where
    unlessImACanceledDo t := do
      if ← IO.checkCanceled
        then do
          -- dbg_trace s!"[producer to channel ({prodIdx})] I was cancelled, exiting"
          return .unit
        else t

inductive MergeError
  | selectOneError (err : IO.Error)
  | waitSelectOneTask (err : IO.Error)
  | weTriedToSendToChannelOrCloseChannelAndFailed
    (errorAndProducerIdxs : Array (Nat × Std.CloseableChannel.Error))
    (errorAndProducerIdxsNotEmpty : ¬(errorAndProducerIdxs = #[]))
  deriving Inhabited

instance : ToString MergeError where
  toString
    | .selectOneError err =>
        s!"[mergeProducers] Failed while selecting on channels: {err.toString}"
    | .waitSelectOneTask err =>
        s!"[mergeProducers] Failed while waiting for channel readiness: {err.toString}"
    | .weTriedToSendToChannelOrCloseChannelAndFailed errs h =>
      match errs with
        | #[] => absurd rfl h
        | #[(idx, e)] =>
          s!"[mergeProducers] Producer {idx} failed while closing or sending to its channel: {e}"
        | _ =>
          let entries := errs.map (fun (idx, e) => s!"producer {idx}: {e}")
          s!"[mergeProducers] Multiple producers failed while closing/sending: {String.intercalate "; " entries.toList}"

instance : MonadLift (EIO MergeError) IO where
  monadLift x := EIO.toIO (.userError <| toString ·) x

def mergeProducers.waitForFinishedTask
  (t : Task (Except Std.CloseableChannel.Error Unit))
  (prodIdx : Nat) :
  BaseIO (Option (Nat × Std.CloseableChannel.Error)) := do
  dbg_trace "[filterMapper]   doing prodIdx {prodIdx}";
  match ← IO.wait t with
    | .error e => return .some (prodIdx, e)
    | .ok .unit => return .none

private abbrev C_T_Id o := Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error Unit) × Nat

def mergeProducers.loopTaskM [ToString o]
  (chsAndTasks : Array (C_T_Id o)) :
  EIO MergeError (Option o × Array (C_T_Id o)) := do
  let selectables := chsAndTasks.filterMap fun (ch, _, prodIdx) =>
    .some $ Std.Internal.IO.Async.Selectable.case ch.recvSelector fun (data : Option o) =>
      return Std.Internal.IO.Async.AsyncTask.pure (data, prodIdx)

  dbg_trace s!"[loop] waiting on {chsAndTasks.size} channels"
  let attTask <- Std.Internal.IO.Async.Selectable.one selectables |>.toEIO MergeError.selectOneError
  let att ← IO.wait attTask
  dbg_trace s!"[loop] got att = {att}"
  let (data, prodIdxThatSentData) ← EIO.ofExcept (att.mapError MergeError.waitSelectOneTask)
  dbg_trace s!"[loop] received data = {data}, prodIdx = {prodIdxThatSentData}"

  -- Only handle the specific producer that sent data
  match data with
  | some _value =>
    -- Producer sent data, keep all producers
    return (data, chsAndTasks)
  | none =>
    -- Producer ended, remove it and close its channel
    let (toClose, toKeep) := chsAndTasks.partition fun (_, _, prodIdx) => prodIdx == prodIdxThatSentData

    -- Close the channel for the ended producer
    let closeErrors ← toClose.filterMapM fun (_ch, t, prodIdx) =>
      mergeProducers.waitForFinishedTask t prodIdx

    if h : closeErrors = #[] then
      return (none, toKeep)
    else
      throw (MergeError.weTriedToSendToChannelOrCloseChannelAndFailed closeErrors h)

private partial def mergeProducers.loopTask
  [ToString o]
  (chsAndTasks : Array (C_T_Id o))
  : Producer o (EIO MergeError) Unit :=
    if chsAndTasks.isEmpty then
      Proxy.Pure .unit
    else
      Proxy.M (mergeProducers.loopTaskM chsAndTasks) fun ((data, chsAndTAndProdIdx) : (_ × Array (_ × _ × _))) =>
        dbg_trace s!"[loopTask] got data={data}"
        match data with
        | .some value => Proxy.Respond value fun _ => mergeProducers.loopTask chsAndTAndProdIdx
        | .none       => mergeProducers.loopTask chsAndTAndProdIdx

def mergeProducers
  [ToString o]
  -- [Monad m]
  -- [MonadLift m (EIO Std.CloseableChannel.Error)]
  (producers : Array (Producer o BaseIO PUnit)) :
  Producer o (EIO MergeError) Unit :=
  if producers.isEmpty then
    Proxy.Pure .unit
  else
    Proxy.M ( do
      dbg_trace "[mergeProducers] starting";
      let chsAndTasks ← producers.mapIdxM fun prodIdx prod => do
        let ch ← Std.CloseableChannel.new
        let t ← EIO.asTask (
          try
            runProducerToChannel prodIdx prod ch
          finally
            ch.close) -- unwraps a producer like an onion, when nothing - just returns
        pure (ch, t, prodIdx)
      pure chsAndTasks
    ) mergeProducers.loopTask
