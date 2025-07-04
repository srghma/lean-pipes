import Mathlib.CategoryTheory.Category.Basic
import Pipes.Core
import Pipes.CoreLaws

namespace PipesLawsCore

-- Respond Category
section RespondCategory

instance RespondCategory {a' a : Type u} {m : Type u -> Type u} :
  CategoryTheory.Category (Type u × Type u) where
  Hom X Y := X.2 → Proxy a' a Y.1 Y.2 m X.1
  id X := Proxy.respond
  comp f g := f />/ g -- fun a => f a //> g
  id_comp := by
    intro X Y f
    funext arg
    obtain ⟨r, argT⟩ := X
    obtain ⟨b, b'⟩ := Y
    simp_all
    induction f arg with
    | Pure a' => rfl
    | Respond b k ih => simp_all [Proxy.bind]
    | Request x' k ih => simp_all [Proxy.bind]
    | M mx ih => simp_all [Proxy.bind]
  comp_id := by
    intro X Y f
    funext arg
    obtain ⟨r, argT⟩ := X
    obtain ⟨b, b'⟩ := Y
    simp_all
    induction f arg with
    | Pure a' => rfl
    | Respond b k ih => simp_all [Proxy.bind]
    | Request x' k ih => simp_all
    | M mx ih => simp_all
  assoc := by
    intro X Y W Z f g h
    funext arg
    obtain ⟨fst, snd⟩ := X
    obtain ⟨fst_1, snd_1⟩ := Y
    obtain ⟨fst_2, snd_2⟩ := W
    obtain ⟨fst_3, snd_3⟩ := Z
    simp_all only
    induction f arg with
    | Pure a' => rfl
    | Respond b k ih =>
      simp_all
      induction g b with
      | Pure a'2 => simp_all [Proxy.bind]
      | Respond b2 k2 ih2 =>
        simp_all
        induction h b2 with
        | Pure a'2 => simp_all [Functor.map, Bind.bind, Proxy.bind, Proxy.forP]
        | Respond b2 k2 ih2 => simp_all [Proxy.bind]
        | Request x' k ih => simp_all [Proxy.bind]
        | M mx ih => simp_all [Proxy.bind]
      | Request x' k ih => simp_all [Proxy.bind]
      | M mx ih => simp_all [Proxy.bind]
    | Request x' k ih => simp_all [Proxy.bind]
    | M mx ih => simp_all

end RespondCategory

section RequestCategory

instance RequestCategory {b' b : Type u} {m : Type u → Type u} :
  CategoryTheory.Category (Type u × Type u) where
  Hom Y X := X.1 → Proxy Y.1 Y.2 b' b m X.2
  id X := Proxy.request
  comp f g := f \>\ g
  id_comp := by
    intro X Y f
    funext arg
    obtain ⟨r, argT⟩ := X
    obtain ⟨b, b'⟩ := Y
    simp_all
    induction f arg with
    | Pure r => rfl
    | Request a k ih => simp_all
    | Respond x' k ih => simp_all
    | M mx k ih => simp_all
  comp_id := by
    intro X Y f
    funext arg
    obtain ⟨r, argT⟩ := X
    obtain ⟨b, b'⟩ := Y
    simp_all
    induction f arg with
    | Pure r => rfl
    | Request a k ih => simp_all
    | Respond x' k ih => simp_all
    | M mx k ih => simp_all
  assoc := by
    intro X Y W Z f g h
    funext arg
    obtain ⟨Xb', Xb⟩ := X
    obtain ⟨Ya', Ya⟩ := Y
    obtain ⟨Wb', Wb⟩ := W
    obtain ⟨Za', Za⟩ := Z
    simp only [Prod.fst, Prod.snd] at g h f arg
    dsimp
    induction h arg with
    | Pure r => rfl
    | Request a k ih =>
      simp_all
      induction g a with
      | Pure r => simp_all
      | Request a' k' ih' =>
        simp_all
        induction f a' with
        | Pure r => simp_all
        | Request a'' k'' ih'' => simp_all
        | Respond x' k ih => simp_all
        | M mx k ih => simp_all
      | Respond x' k ih => simp_all
      | M mx k ih => simp_all
    | Respond x' k ih => simp_all
    | M mx k ih => simp_all

end RequestCategory

section PushCategory

private axiom Unbounded.push.eq_def_assuming_infinity [Inhabited r] : ∀ xa, Proxy.Unbounded.push (a := a) (a' := a') (m := m) (r := r) xa =
  (.Respond xa (fun x => .Request x (Proxy.Unbounded.push)))
  in
def Unbounded.PushCategory [Inhabited r] (m : Type u -> Type u):
  CategoryTheory.Category (Type u × Type u) where
  Hom A B := B.2 → Proxy B.1 B.2 A.1 A.2 m r
  id A := Proxy.Unbounded.push
  comp f g := g >~> f --  fun a => g a >>~ f
  id_comp := by
    intro ⟨b', b⟩ ⟨a', a⟩ f
    funext arg
    simp only [Prod.fst, Prod.snd] at f arg
    dsimp
    induction f arg with
    | Pure r => simp [Proxy.pushR, Proxy.pushR.go]
    | Request a k ih => simp [Proxy.pushR, Proxy.pushR.go, ih]
    | M mx k ih => simp [Proxy.pushR, Proxy.pushR.go, ih]
    | Respond xb k ih =>
      simp [Proxy.pushR, Proxy.pushR.go, ih]
      rw [push.eq_def_assuming_infinity]
      simp [Proxy.pushR, Proxy.pushR.go, ih]
  comp_id := by
    intro X Y f
    funext arg
    obtain ⟨r, argT⟩ := X
    obtain ⟨b, b'⟩ := Y
    simp only [Prod.fst, Prod.snd] at f arg
    simp_all
    rw [push.eq_def_assuming_infinity]
    simp only [Proxy.pushR]
    induction f arg with
    | Pure r => simp_all [Proxy.pushR, Proxy.pushR.go]
    | Request a k ih =>
      simp_all [Proxy.pushR, Proxy.pushR.go]
      funext arg
      rw [push.eq_def_assuming_infinity]
      simp_all [Proxy.pushR, Proxy.pushR.go]
    | Respond x' k ih => simp_all [Proxy.pushR, Proxy.pushR.go]
    | M mx k ih => simp_all [Proxy.pushR, Proxy.pushR.go]
  assoc := by
    dsimp
    intro X Y W Z f g h
    funext arg
    obtain ⟨Xb', Xb⟩ := X
    obtain ⟨Ya', Ya⟩ := Y
    obtain ⟨Wb', Wb⟩ := W
    obtain ⟨Za', Za⟩ := Z
    simp only [Prod.fst, Prod.snd] at g h f arg
    apply PushCategory.push_assoc

/-
private axiom Hpull {r a m} (n : ℕ) (d : r) (xa' : a') :
    Proxy.Fueled.pull (a := a) (m := m) d n xa' = Proxy.Fueled.pull d (n + 1) xa'

private axiom Hpush (n : ℕ) (d : r) :
    Proxy.Fueled.push (a := a) (a' := a') (m := m) d n = Proxy.Fueled.push d (n + 1)

variable
  (r : Type u)  (m : Type u → Type u)
  (default : r) (fuel : Nat) (fuelNE0 : fuel + 1 ≠ 0)
    [Inhabited r] in
instance Fueled.PushCategory :
  CategoryTheory.Category (Type u × Type u) where
  Hom A B := B.2 → Proxy B.1 B.2 A.1 A.2 m r
  id A := Proxy.Fueled.push default fuel
  comp f g := g >~> f --  fun a => g a >>~ f
  id_comp := by
    intro ⟨b', b⟩ ⟨a', a⟩ f
    funext arg
    simp only [Prod.fst, Prod.snd] at f arg
    dsimp
    induction f arg with
    | Pure r => simp_all
    | Request a k ih => simp_all
    | M mx k ih => simp_all
    | Respond xb k ih =>
      rw [Hpush]
      induction h : fuel + 1 with
      | zero => contradiction
      | succ fuel' ih2 =>
        -- generalize h :  Proxy.Fueled.push default fuel' = xxx
        rw [Hpush]
        sorry -- exact ih2
  comp_id := sorry
  assoc := sorry
-/

end PushCategory

section PullCategory

private axiom Unbounded.pull.eq_def_assuming_infinity [Inhabited r] : ∀ xa, Proxy.Unbounded.pull (a := a) (a' := a') (m := m) (r := r) xa =
  (.Request xa (fun x => .Respond x (Proxy.Unbounded.pull)))
  in
def Unbounded.PullCategory [Inhabited r] (m : Type u -> Type u):
  CategoryTheory.Category (Type u × Type u) where
  Hom A B := A.1 → Proxy B.1 B.2 A.1 A.2 m r
  id A := Proxy.Unbounded.pull
  comp f g := g >+> f --  fun a => g +>> f a
  id_comp := by
    intro ⟨b', b⟩ ⟨a', a⟩ f
    funext arg
    simp only [Prod.fst, Prod.snd] at f arg
    dsimp
    rw [pull.eq_def_assuming_infinity]
    simp [Proxy.pullR, Proxy.pullR.go]
    induction f arg with
    | Pure r => simp [Proxy.pullR, Proxy.pullR.go]
    | Request a k ih => simp [Proxy.pullR, Proxy.pullR.go, ih]
    | M mx k ih => simp [Proxy.pullR, Proxy.pullR.go, ih]
    | Respond xb k ih =>
      simp [Proxy.pullR, Proxy.pullR.go, ih]
      funext karg
      rw [pull.eq_def_assuming_infinity]
      simp [Proxy.pullR, Proxy.pullR.go, ih]
  comp_id := by
    intro X Y f
    funext arg
    obtain ⟨r, argT⟩ := X
    obtain ⟨b, b'⟩ := Y
    simp only [Prod.fst, Prod.snd] at f arg
    simp_all
    induction f arg with
    | Pure r => simp_all [Proxy.pullR, Proxy.pullR.go]
    | Request a k ih =>
      simp_all [Proxy.pullR, Proxy.pullR.go]
      rw [pull.eq_def_assuming_infinity]
      simp_all [Proxy.pullR, Proxy.pullR.go]
    | Respond x' k ih => simp_all [Proxy.pullR, Proxy.pullR.go]
    | M mx k ih => simp_all [Proxy.pullR, Proxy.pullR.go]
  assoc := by
    dsimp
    intro X Y W Z f g h
    funext arg
    obtain ⟨Xb', Xb⟩ := X
    obtain ⟨Ya', Ya⟩ := Y
    obtain ⟨Wb', Wb⟩ := W
    obtain ⟨Za', Za⟩ := Z
    simp only [Prod.fst, Prod.snd] at g h f arg
    apply PullCategory.pull_assoc
