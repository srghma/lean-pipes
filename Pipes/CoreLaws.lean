import Aesop
import Canonical
-- import Mathlib.CategoryTheory.Category.Basic
import Pipes.Internal
import Pipes.Core
import Canonical
import Mathlib.Data.Nat.Init
import Init.Ext

namespace PipesLawsCore

-- Respond Category
section RespondCategory

-- Respond distributivity theorem
theorem respondDistrib [Monad m]
  (f : a → Proxy x' x b' b m a')
  (g : a' → Proxy x' x b' b m r)
  (h : b → Proxy x' x c' c m b') :
  (f >=> g) />/ h = (f />/ h) >=> (g />/ h) := by
  funext a
  simp_all [(· >=> ·), Bind.bind]
  induction f a with
  | Pure a' => rfl
  | Respond b k ih =>
    simp_all
    induction h b with
    | Pure a' => rfl
    | Respond b k ih => simp_all
    | Request x' k ih => simp_all
    | M mx ih => simp_all
  | Request x' k ih => simp_all
  | M mx ih => simp_all

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
    | Respond b k ih => simp_all
    | Request x' k ih => simp_all
    | M mx ih => simp_all
  comp_id := by
    intro X Y f
    funext arg
    obtain ⟨r, argT⟩ := X
    obtain ⟨b, b'⟩ := Y
    simp_all
    induction f arg with
    | Pure a' => rfl
    | Respond b k ih => simp_all
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
      | Pure a'2 => simp_all
      | Respond b2 k2 ih2 =>
        simp_all
        induction h b2 with
        | Pure a'2 => simp_all
        | Respond b2 k2 ih2 => simp_all
        | Request x' k ih => simp_all
        | M mx ih => simp_all
      | Request x' k ih => simp_all
      | M mx ih => simp_all
    | Request x' k ih => simp_all
    | M mx ih => simp_all


theorem respondZero (someR : r) (f : c → Proxy a' a b' b m r): (Proxy.Pure />/ f) someR = Proxy.Pure someR := by rfl

end RespondCategory

section RequestCategory

theorem requestDistrib
  (f : c → Proxy b' b y' y m c')
  (g : c' → Proxy b' b y' y m r)
  (h : b' → Proxy a' a y' y m b) :
  h \>\ (f >=> g) = (h \>\ f) >=> (h \>\ g) := by
  funext x
  simp_all [(· >=> ·), Bind.bind]
  induction f x with
  | Pure a' => rfl
  | Respond b k ih => simp_all
  | Request x' k ih =>
    simp_all
    induction h x' with
    | Pure a' => rfl
    | Respond b k ih => simp_all
    | Request x' k ih => simp_all
    | M mx ih => simp_all
  | M mx ih => simp_all

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

theorem requestZero (someR : r) (f : c → Proxy a' a b' b m r): (f \>\ Proxy.Pure) someR = Proxy.Pure someR := by rfl

end RequestCategory

section PushCategory

theorem pushRequest
  (f : b → Proxy b' b c' c m r)
  (g : a → Proxy a' a b' b m r)
  (x : a') :
  Proxy.Request x g >>~ f = Proxy.Request x (g >~> f) := by simp only [Proxy.pushR]

theorem pushRequest'
  (f : b → Proxy b' b c' c m r)
  (g : a → Proxy a' a b' b m r)
  (x : a') :
  Proxy.pushR (Proxy.Request x g) f = Proxy.Request x (fun a => Proxy.pushR (g a) f) := by simp only [Proxy.pushR]

theorem pushM
  (f : b → Proxy b' b c' c m r)
  (g : x → Proxy a' a b' b m r)
  (h : m x) :
  Proxy.M h g >>~ f = Proxy.M h (g >~> f) := by simp only [Proxy.pushR]

theorem push_assoc (p : Proxy Za' Za Wb' Wb m r) (f : Ya → Proxy Ya' Ya Xb' Xb m r) (g : Wb → Proxy Wb' Wb Ya' Ya m r) :
  (p >>~ fun a => g a >>~ f) = p >>~ g >>~ f := by
  induction p generalizing f g with
  | Pure r => simp [Proxy.pushR]
  | M mx k ih => simp [Proxy.pushR, ih]
  | Request a k ih =>  simp [Proxy.pushR, ih]
  | Respond x k ih =>
    simp [Proxy.pushR]
    induction g x generalizing k f with
    | Pure r => simp [Proxy.pushR, Proxy.pushR.go]
    | M mx k ih2 => simp [Proxy.pushR, Proxy.pushR.go, ih, ih2]
    | Request a2 k2 ih2 => simp [Proxy.pushR, Proxy.pushR.go, ih]
    | Respond x2 k2 ih2 =>
      simp [Proxy.pushR, Proxy.pushR.go]
      induction f x2 generalizing k k2 with
      | Pure r => simp [Proxy.pushR.go]
      | M mx k ih3 => simp_all [Proxy.pushR.go]
      | Respond x3 k3 ih3 => simp_all [Proxy.pushR.go]
      | Request a3 k3 ih3 => simp_all [Proxy.pushR.go]

-- Push Category instance

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
    apply push_assoc

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

-- Pull Category
section PullCategory

@[simp] theorem pullRespond
    (f : b' → Proxy a' a b' b m r)
    (g : c' → Proxy b' b c' c m r)
    (x : c) :
  f +>> Proxy.Respond x g = Proxy.Respond x (f >+> g) := by simp_all [Proxy.pullR]

@[simp] theorem pullM
    (f : b' → Proxy a' a b' b m r)
    (g : x → Proxy b' b c' c m r)
    (h : m x) :
  f +>> Proxy.M h g = Proxy.M h (f >+> g) := by simp_all [Proxy.pullR]

theorem pull_assoc
  (p : Proxy Ya' Ya Xb' Xb m r)
  (g : Ya' → Proxy Wb' Wb Ya' Ya m r)
  (h : Wb' → Proxy Za' Za Wb' Wb m r) :
  h +>> (g +>> p) = (fun a => h +>> g a) +>> p := by
  induction p generalizing h g with
  | Pure r => simp [Proxy.pullR]
  | M mx k ih => simp_all [Proxy.pullR, Proxy.pullR.go, ih]
  | Request a k ih =>
    simp [Proxy.pullR]
    induction g a generalizing k h with
    | Pure r => simp [Proxy.pullR, Proxy.pullR.go]
    | M mx k ih2 => simp [Proxy.pullR, Proxy.pullR.go, ih, ih2]
    | Respond x2 k2 ih2 => simp [Proxy.pullR, Proxy.pullR.go, ih, ih2]
    | Request a2 k2 ih2 =>
      simp [Proxy.pullR, Proxy.pullR.go]
      induction h a2 generalizing k k2 with
      | Pure r => simp [Proxy.pullR.go]
      | M mx k ih3 => simp_all [Proxy.pullR.go]
      | Respond x3 k3 ih3 => simp_all [Proxy.pullR.go]
      | Request a3 k3 ih3 => simp_all [Proxy.pullR.go]
  | Respond x k ih => simp_all [Proxy.pullR, Proxy.pullR.go, ih]

-- Push Category instance

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
    apply pull_assoc

theorem pushPullAssoc -- [Monad m] [LawfulMonad m]
  (f : b' → Proxy a' a b' b m r)
  (g : a  → Proxy b' b c' c m r)
  (h : c  → Proxy c' c b' b m r) :
  (f >+> g) >~> h = f >+> (g >~> h) := by
    dsimp
    funext arg
    induction g arg generalizing f h with
    | Pure r => simp [Proxy.pullR, Proxy.pushR]
    | M mx k ih => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
    | Request a k ih =>
      simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
      induction f a generalizing k h with
      | Pure r => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
      | M mx k ih => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
      | Request a2 k2 ih2 => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
      | Respond x2 k2 ih2 => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
    | Respond x k ih =>
      simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
      induction h x generalizing k f with
      | Pure r => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
      | M mx k ih => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
      | Request a2 k2 ih2 => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]
      | Respond x2 k2 ih2 => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go, ih]

end PullCategory

section Duals

theorem requestId : Proxy.reflect ∘ Proxy.request = @Proxy.respond a' a b' b m := by
  funext x
  simp [Proxy.reflect, Proxy.request, Proxy.respond]

theorem reflectDistrib (f : a → Proxy a' a b' b m r)
                       (g : r → Proxy a' a b' b m r) (x : a) :
  Proxy.reflect (f x >>= g) = Proxy.reflect (f x) >>= (Proxy.reflect ∘ g) := by
    simp_all [Bind.bind]
    induction f x with
    | Pure a' => rfl
    | Respond b k ih => simp_all
    | Request x' k ih => simp_all
    | M mx ih => simp_all

theorem requestComp (f : a → Proxy a' a b' b m r)
                    (g : a → Proxy a r b' b m r) :
  Proxy.reflect ∘ (f \>\ g) = (Proxy.reflect ∘ g) />/ (Proxy.reflect ∘ f) := by
  funext x
  simp_all
  induction g x with
  | Pure a' => simp_all
  | Respond b k ih => simp_all
  | Request x' k ih =>
    simp_all
    induction f x' with
    | Pure a' => simp_all
    | Respond b k ih => simp_all
    | Request x' k ih => simp_all
    | M mx ih => simp_all
  | M mx ih => simp_all

theorem respondId : Proxy.reflect ∘ Proxy.respond = @Proxy.request a' a b' b m := by
  funext x
  simp

theorem respondComp (f : a → Proxy a' a b' b m r)
                    (g : b → Proxy a' a b' b m b') :
  Proxy.reflect ∘ (f />/ g) = (Proxy.reflect ∘ g) \>\ (Proxy.reflect ∘ f) := by
  funext x
  simp
  induction (f x) with
  | Request a' k ih => simp_all
  | Respond b k ih =>
    simp_all
    induction (g b) with
    | Request a' k ih => simp_all
    | Respond b k ih => simp_all
    | M mx k ih => simp_all
    | Pure r => simp_all
  | M mx k ih => simp_all
  | Pure r => simp

theorem distributivity (f : a → Proxy a' a b' b m r)
                       (g : r → Proxy a' a b' b m r) :
  Proxy.reflect ∘ (f >=> g) = (Proxy.reflect ∘ f) >=> (Proxy.reflect ∘ g) := funext (reflectDistrib f g)

theorem zeroLaw (x : r) : Proxy.reflect (pure x : Proxy a' a b' b m r) = (pure x : Proxy b b' a a' m r) := by
  simp [pure]

theorem involution (p : Proxy a' a b' b m r) : Proxy.reflect (Proxy.reflect p) = p := by
  induction p with
  | Request xa' k ih =>
    simp
    funext a
    exact ih a
  | Respond xb k ih =>
    simp
    funext b'
    exact ih b'
  | M mx k ih =>
    simp
    funext x
    exact ih x
  | Pure xr =>
    simp

end Duals
end PipesLawsCore
