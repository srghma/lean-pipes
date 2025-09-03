import Pipes.Internal
import Pipes.Core
import Pipes.Prelude
import Pipes.Extra.Array
import Std.Sync.Mutex
import Std.Sync.Channel
import Std.Internal.Async.Basic
import Std.Internal.Async.Select
import Init.System.IO

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
I unwrap a producer like an onion.
I just send, I dont close channel (even if my thread was canceled), user should do this,
I can only fail in `Std.CloseableChannel.send` if channel was closed but I tried to send value (which is impossible by logic really)
-/
-- TODO: split on `runProducerToChannel_inTask : .. -> EIO Std.CloseableChannel.Error (Option r)` and `runProducerToChannel_inMain : .. -> EIO Std.CloseableChannel.Error r`
def runProducerToChannel
  -- [ToString o]
  -- [Monad m]
  -- [MonadLift m (EIO Std.CloseableChannel.Error)]
  (prodIdx : Nat)
  (p : Producer o BaseIO r)
  (ch : Std.CloseableChannel o) :
  EIO Std.CloseableChannel.Error (Option r) :=
  match p with
  | .Request v _k => PEmpty.elim v
  | .Pure r => do
    -- dbg_trace s!"[producer to channel ({prodIdx})] return .unit"
    return .some r
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
          return .none
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
  (t : Task (Except Std.CloseableChannel.Error (Option r)))
  (prodIdx : Nat) :
  BaseIO (Except (Nat × Std.CloseableChannel.Error) (Option r)) := do
  -- dbg_trace "[filterMapper]   doing prodIdx {prodIdx}";
  match ← IO.wait t with
    | .error e => return .error (prodIdx, e)
    | .ok r => return .ok r

def Except.toSum : Except a b -> Sum a b | error a => Sum.inl a | ok b => Sum.inr b

private abbrev C_T_Id o r := Std.CloseableChannel o × Task (Except Std.CloseableChannel.Error (Option r)) × Nat

def mergeProducers.loopTaskM
  -- [ToString o]
  (chsAndTasks : Array (C_T_Id o r)) :
  EIO MergeError (Option o × Array (C_T_Id o r) × Array r) := do
  let selectables := chsAndTasks.filterMap fun (ch, _, prodIdx) =>
    .some $ Std.Internal.IO.Async.Selectable.case ch.recvSelector fun (data : Option o) =>
      return Std.Internal.IO.Async.AsyncTask.pure (data, prodIdx)

  -- dbg_trace s!"[loop] waiting on {chsAndTasks.size} channels"
  let attTask <- Std.Internal.IO.Async.Selectable.one selectables |>.toEIO MergeError.selectOneError
  let att ← IO.wait attTask
  -- dbg_trace s!"[loop] got att = {att}"
  let (data, prodIdxThatSentData) ← EIO.ofExcept (att.mapError MergeError.waitSelectOneTask)
  -- dbg_trace s!"[loop] received data = {data}, prodIdx = {prodIdxThatSentData}"

  match data with
  | some _value => return (data, chsAndTasks, #[])
  | none =>
    -- if none then channel was closed already (by parallel task, means task was consumed)
    -- Why not to close in main thread? Before I closed in main but got into problems
    let (toClose, toKeep) := chsAndTasks.partition fun (_, _, prodIdx) => prodIdx == prodIdxThatSentData

    let (closeErrors, (returns : Array (Option r))) ← toClose.partitionMapM fun (_ch, t, prodIdx) =>
      Functor.map Except.toSum (mergeProducers.waitForFinishedTask t prodIdx) -- take out the errors from task if any

    if h : closeErrors = #[] then
      return (.none, toKeep, returns.filterMap id)
    else
      throw (MergeError.weTriedToSendToChannelOrCloseChannelAndFailed closeErrors h)

private partial def mergeProducers.loopTask
  -- [ToString o]
  (oldReturns : Array r)
  (chsAndTasks : Array (C_T_Id o r))
  : Producer o BaseIO (Except MergeError (Array r)) :=
    if chsAndTasks.isEmpty then
      Proxy.Pure (.ok oldReturns)
    else
      Proxy.M ((mergeProducers.loopTaskM chsAndTasks).toBaseIO) fun
        | .error e => return .error e
        | .ok ((data, chsAndTAndProdIdx, returns) : (_ × Array (_ × _ × _) × Array r)) =>
          -- dbg_trace s!"[loopTask] got data={data}"
          match data with
          | .some value => Proxy.Respond value fun _ => mergeProducers.loopTask (oldReturns ++ returns) chsAndTAndProdIdx
          | .none       => mergeProducers.loopTask (oldReturns ++ returns) chsAndTAndProdIdx

def mergeProducers
  -- [ToString o]
  -- [Monad m]
  -- [MonadLift m (EIO Std.CloseableChannel.Error)]
  (producers : Array (Producer o BaseIO r)) : -- BaseIO instead of IO to tell that we dont handle errors
  Producer o BaseIO (Except MergeError (Array r)) :=
  if producers.isEmpty then
    Proxy.Pure (.ok #[])
  else
    Proxy.M ( do
      -- dbg_trace "[mergeProducers] starting";
      let chsAndTasks ← producers.mapIdxM fun prodIdx prod => do
        let ch ← Std.CloseableChannel.new
        let t ← EIO.asTask (
          try
            runProducerToChannel prodIdx prod ch
          finally
            ch.close)
        pure ((ch, t, prodIdx) : C_T_Id o r)
      pure chsAndTasks
    ) (fun chsAndTasks => mergeProducers.loopTask #[] chsAndTasks)
