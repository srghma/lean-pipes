import Mathlib.Data.PFunctor.Univariate.Basic

universe u v

/-- The free monad on a polynomial functor.
This extends the `W`-type construction with an extra `pure` constructor. -/
inductive FreeM (P : PFunctor.{u}) : Type v → Type (max u v)
  | pure {α} (x : α) : FreeM P α
  | roll {α} (a : P.A) (r : P.B a → FreeM P α) : FreeM P α
deriving Inhabited

/-- Lift an object of the base polynomial functor into the free monad. -/
@[always_inline, inline]
def FreeM.lift (x : P.Obj α) : FreeM P α := FreeM.roll x.1 (fun y ↦ FreeM.pure (x.2 y))

/-- Bind operator on `FreeM P` operation used in the monad definition. -/
@[always_inline, inline]
def FreeM.bind : FreeM P α → (α → FreeM P β) → FreeM P β
  | FreeM.pure x, g => g x
  | FreeM.roll x r, g => FreeM.roll x (λ u ↦ FreeM.bind (r u) g)
