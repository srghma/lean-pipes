import Pipes.Internal
import Pipes.Core
import Pipes.Prelude
import Pipes.Debug

def mergePureProducersConcat.loop (returns : List r) (producers : List (Producer o m r)) : Producer o m (List r) := do
  match producers with
  | [] => Proxy.Pure returns.reverse
  | p :: rest => p.bind fun r => loop (r :: returns) rest

def mergePureProducersConcat (producers : List (Producer o m r)) : Producer o m (List r) := mergePureProducersConcat.loop [] producers

----------------------------------------------------------------------------
private partial def mergePureProducersRoundRobit.loop (returns : List r) (ps : List (Producer o m r)) (acc : List (Producer o m r)) : Producer o m (List r) := do
  match ps with
  | [] =>
      if acc.isEmpty then
        Proxy.Pure returns.reverse
      else
        mergePureProducersRoundRobit.loop returns acc [] -- if `acc.reverse` then `TwoRound` instead of `RoundRobin`
  | p :: rest =>
      match p with
      | Proxy.Respond x k => Proxy.Respond x (fun _ => mergePureProducersRoundRobit.loop returns rest (k () :: acc))
      | Proxy.Pure r => mergePureProducersRoundRobit.loop (r :: returns) rest acc
      | Proxy.Request v _ => PEmpty.elim v
      -- | Proxy.M op k => Proxy.M op (fun x => mergePureProducersRoundRobit.loop (returns) ((k x) :: rest) (acc)) -- current thread is prioritized
      | Proxy.M op k => Proxy.M op (fun x => mergePureProducersRoundRobit.loop returns rest ((k x) :: acc)) -- switch to next thread
  -- termination_by ps.length + acc.length
  -- decreasing_by
  --   sorry

partial def mergePureProducersRoundRobit (producers : List (Producer o m r)) : Producer o m (List r) := mergePureProducersRoundRobit.loop [] producers []

----------------------------------------------------------------------------

#guard  (['1', '2', '3'], [1, 11, 111, 2, 22, 3, 33]) = (Proxy.toList $
  mergePureProducersConcat [
    (fun .unit => '1') <$> Proxy.fromList [1, 11, 111],
    (fun .unit => '2') <$> Proxy.fromList [2, 22],
    (fun .unit => '3') <$> Proxy.fromList [3, 33]
  ])

def example1: Producer Nat Id (List Char) :=
  mergePureProducersRoundRobit [
    (fun .unit => '1') <$> Proxy.fromList [1, 11, 111],
    (fun .unit => '2') <$> Proxy.fromList [2, 22],
    (fun .unit => '3') <$> Proxy.fromList [3, 33]
  ]

#guard  (['2', '3', '1'], [1, 2, 3, 33, 22, 11, 111]) = Proxy.toList example1
-- #eval Proxy.toList example1
-- #eval Pipes.Debug.debugProducer example1
