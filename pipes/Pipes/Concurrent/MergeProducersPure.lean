import Pipes.Internal
import Pipes.Core
import Pipes.Prelude

open Std

def mergePureProducersConcat (producers : List (Producer o Id PUnit)) : Producer o Id PUnit := do
  match producers with
  | [] => Proxy.Pure ()
  | p :: rest => p.bind fun _ => mergePureProducersConcat rest

----------------------------------------------------------------------------
private partial def mergePureProducersTwoPhase.loop (ps : List (Producer o Id PUnit)) (acc : List (Producer o Id PUnit)) : Producer o Id PUnit := do
  match ps with
  | [] =>
      if acc.isEmpty then
        Proxy.Pure ()
      else
        mergePureProducersTwoPhase.loop (acc.reverse) []
  | p :: rest =>
      match p with
      | Proxy.Respond x k => Proxy.Respond x (fun _ => mergePureProducersTwoPhase.loop rest (k () :: acc))
      | Proxy.Pure _ => mergePureProducersTwoPhase.loop rest acc
      | Proxy.Request v _ => PEmpty.elim v
      | Proxy.M op k => k (Id.run op)  -- Since m = Id, run the effect directly
  -- termination_by ps.length + acc.length
  -- decreasing_by
  --   sorry

partial def mergePureProducersTwoPhase (producers : List (Producer o Id PUnit)) : Producer o Id PUnit := mergePureProducersTwoPhase.loop producers []

----------------------------------------------------------------------------
private def mergePureProducersRoundRobin.stepAll (ps : List (Producer o Id PUnit)) : List (Producer o Id PUnit) × List o :=
  ps.foldl (fun (acc, outputs) p =>
    match p with
    | Proxy.Respond x k => (k () :: acc, x :: outputs)
    | Proxy.Pure _ => (acc, outputs)
    | Proxy.Request v _ => PEmpty.elim v
    | Proxy.M op k => (k (Id.run op) :: acc, outputs)
  ) ([], [])

private def mergePureProducersRoundRobin.emitOutputs (xs : List o) (next : Producer o Id PUnit) : Producer o Id PUnit :=
  match xs with
  | [] => next
  | y :: ys => Proxy.Respond y (fun _ => mergePureProducersRoundRobin.emitOutputs ys next)

partial def mergePureProducersRoundRobin (ps : List (Producer o Id PUnit)) : Producer o Id PUnit :=
  match ps with
  | [] => Proxy.Pure ()
  | x :: rest =>
      let (nextProducers, outputs) := mergePureProducersRoundRobin.stepAll (x :: rest)
      -- have h : nextProducers.length ≤ ps.length := by
      --   sorry
      mergePureProducersRoundRobin.emitOutputs outputs.reverse (mergePureProducersRoundRobin nextProducers)

----------------------------------------------------------------------------

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
