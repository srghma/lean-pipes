import Pipes.Internal
import Pipes.Core
import Pipes.Prelude

private def mergeProducersConcat.List.loop (returns : List r) (producers : List (Producer o m r)) : Producer o m (List r) := do
  match producers with
  | [] => Proxy.Pure returns.reverse
  | p :: rest => p.bind fun r => loop (r :: returns) rest

abbrev mergeProducersConcat.List : List (Producer o m r) -> Producer o m (List r) := mergeProducersConcat.List.loop []

----------------------------------------------------------------------------
def mergeProducersConcat.Array (producers : Array (Producer o m r)) : Producer o m (Array r) :=
  Array.foldlM (as := producers) (init := #[]) fun acc p => return (acc.push (← p))

----------------------------------------------------------------------------
private def mergeProducersRoundRobit.loop (returns : List r) (ps : List (Producer o m r)) : Producer o m (List r) := do
  match ps with
  | [] => Proxy.Pure returns.reverse
  | p :: rest =>
      match p with
      | Proxy.Respond x k => Proxy.Respond x fun .unit => do
        let (newReturns : List r) <- mergeProducersRoundRobit.loop returns rest
        let (kret : r) <- k .unit
        Proxy.Pure (kret :: newReturns)
      | Proxy.Pure r => mergeProducersRoundRobit.loop (r :: returns) rest
      | Proxy.Request v _ => PEmpty.elim v
      | Proxy.M op k => Proxy.M op fun x => do
        let (newReturns : List r) <- mergeProducersRoundRobit.loop returns rest
        let (kret : r) <- k x
        Proxy.Pure (kret :: newReturns)

abbrev mergeProducersRoundRobit : List (Producer o m r) -> Producer o m (List r) := mergeProducersRoundRobit.loop []

----------------------------------------------------------------------------

namespace MergePureProducersTest

def example1: List (Producer Nat Id Char) := [
  (fun .unit => '1') <$> Proxy.fromList [1, 11, 111],
  (fun .unit => '2') <$> Proxy.fromList [2, 22],
  (fun .unit => '3') <$> Proxy.fromList [3, 33]
]

#guard (['1', '2', '3'], [1, 11, 111, 2, 22, 3, 33]) = Proxy.toList (mergeProducersConcat.List example1)
#guard (['1', '2', '3'], [1, 2, 3, 33, 22, 11, 111]) = Proxy.toList (mergeProducersRoundRobit example1)

end MergePureProducersTest
