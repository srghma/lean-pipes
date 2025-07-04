import Mathlib.CategoryTheory.Category.Basic
import Pipes.Internal

namespace Proxy.PipesLawsInternal

def ProxyKleisliCategory
  {a' a b' b : Type u}
  {m : Type u → Type u}
  : CategoryTheory.Category (Type u) where
  Hom A B := A → Proxy a' a b' b m B
  id A := pure
  comp f g := fun x => (f >=> g) x
  id_comp := by
    intros X Y f
    funext x
    rfl
  comp_id := by
    intros X Y f
    funext x
    simp [(· >=> ·)]
  assoc := by
    intros X Y Z W f g h
    funext x
    simp [(· >=> ·)]
