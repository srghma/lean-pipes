import Pipes.Prelude

namespace PipesLawsPrelude

open Proxy

theorem map_id (d : r) (fuel : Nat) :
  Fueled.mapPipe (a := a) (b := a) (m := m) d fuel (fun x => x) = Fueled.cat d fuel := by
  induction fuel with
  | zero => simp only [Fueled.cat, Fueled.pull, Fueled.mapPipe]
  | succ n ih => simp only [Fueled.cat, Fueled.pull, Fueled.mapPipe, ih]

theorem map_compose
  (d : r) (fuel : Nat)
  (f : a → b) (g : b → c) :
  Fueled.mapPipe d fuel (g ∘ f)
    = Fueled.mapPipe d fuel f
      >-> Fueled.mapPipe (m := m) d fuel g := by
        induction fuel with
        | zero => simp only [Fueled.mapPipe, connect, pullR]
        | succ n ih => simp_all [Fueled.mapPipe, connect, pullR, pullR.go]

theorem toListM_each_id [Monad m] [LawfulMonad m] (xs : List a) :
  toListM (each xs) = Pure.pure (f := m) xs := by
  induction xs with
  | nil => simp_all [each, toListM]
  | cons x' xs' ih => simp_all [each, toListM, Bind.bind]

end PipesLawsPrelude
