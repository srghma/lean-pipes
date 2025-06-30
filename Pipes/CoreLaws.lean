import Aesop
import Canonical
-- import Mathlib.CategoryTheory.Category.Basic
import Pipes.Internal
import Pipes.Core
import Pipes.CoreLaws.PullGo
import Pipes.CoreLaws.PushGo
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


theorem respondZeroImpl (someR : r) (f : c → Proxy a' a b' b m r): (Proxy.Pure />/ f) someR = Proxy.Pure someR := by rfl

-- theorem respondZero  {a' a b' b c r : Type u} {m : Type u → Type u} (f : c → Proxy a' a b' b m r) : .Pure />/ f = .Pure := by rfl

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
    obtain ⟨fst, snd⟩ := X
    obtain ⟨fst_1, snd_1⟩ := Y
    obtain ⟨fst_2, snd_2⟩ := W
    obtain ⟨fst_3, snd_3⟩ := Z
    simp_all only
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

theorem requestZeroImpl (someR : r) (f : c → Proxy a' a b' b m r): f >\\ (Proxy.Pure someR) = .Pure someR := by rfl
theorem requestZeroImpl' (someR : r) (f : c → Proxy a' a b' b m r): (f \>\ Proxy.Pure) someR = Proxy.Pure someR := by rfl

-- theorem requestZero (f : c → Proxy a' a b' b m r) : f \>\ Proxy.Pure = Proxy.Pure := by sorry

end RequestCategory

section PushCategory

@[simp] theorem pushRequest
  (f : b → Proxy b' b c' c m r)
  (g : a → Proxy a' a b' b m r)
  (x : a') :
  Proxy.Request x g >>~ f = Proxy.Request x (g >~> f) := by simp_all

@[simp] theorem pushRequest'
  (f : b → Proxy b' b c' c m r)
  (g : a → Proxy a' a b' b m r)
  (x : a') :
  Proxy.pushR (Proxy.Request x g) f = Proxy.Request x (fun a => Proxy.pushR (g a) f) := by simp

@[simp] theorem pushM
  (f : b → Proxy b' b c' c m r)
  (g : x → Proxy a' a b' b m r)
  (h : m x) :
  Proxy.M h g >>~ f = Proxy.M h (g >~> f) := by simp

-- Push Category instance


  -- [Monad m] [LawfulMonad m]

-- lemma Fueled.pushR_push_simplify (fuel : ℕ) (default : r) (x : a) :
--   Proxy.Fueled.push (a' := a') (m := m) default fuel x >>~ Proxy.Fueled.push default fuel =
--   Proxy.Fueled.push default fuel x := by
--   induction fuel with
--   | zero =>
--     simp [Proxy.Fueled.push]
--   | succ fuel' ih =>
--     simp [Proxy.Fueled.push, Proxy.pushR, ih]
--     funext xa'
--     congr 1
--     sorry

    --   -- rcases Nat.exists_eq_succ_of_ne_zero fueledPushFuelIsPositive with ⟨fueledPushFuel', rfl⟩

-- unsafe def Proxy.Unbounded.push {a a' r m} [Inhabited r] : a -> Proxy a' a a' a m r :=
--   (.Respond · (.Request · Proxy.Unbounded.push))

axiom Hpull {r a m} (n : ℕ) (d : r) (xa' : a') :
    Proxy.Fueled.pull (a := a) (m := m) d n xa' = Proxy.Fueled.pull d (n + 1) xa'

axiom Hpush (n : ℕ) (d : r) :
    Proxy.Fueled.push (a := a) (a' := a') (m := m) d (n + 1) = Proxy.Fueled.push d n

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
      rw [← Hpush]
      induction h : fuel + 1 with
      | zero => contradiction
      | succ fuel' ih2 =>
        -- generalize h :  Proxy.Fueled.push default fuel' = xxx
        rw [Hpush]
        exact ih2
  comp_id := sorry
  assoc := sorry

#print Proxy.pushR.eq_def

end PushCategory

-- Pull Category
section PullCategory

@[simp] theorem pullRespond
    (f : b' → Proxy a' a b' b m r)
    (g : c' → Proxy b' b c' c m r)
    (x : c) :
  f +>> Proxy.Respond x g = Proxy.Respond x (f >+> g) := by simp

@[simp] theorem pullM
    (f : b' → Proxy a' a b' b m r)
    (g : x → Proxy b' b c' c m r)
    (h : m x) :
  f +>> Proxy.M h g = Proxy.M h (f >+> g) := by simp

-- instance PullCategory :
--   CategoryTheory.Category (Type u × Type u) where
--   Hom A B := A.1 → Proxy B.1 B.2 A.1 A.2 m r
--   id A := pull
--   comp f g := f >+> g
--   id_comp := by
--     intro A B f
--     funext z
--     sorry
--   comp_id := by
--     intro A B f
--     funext z
--     obtain ⟨fst, snd⟩ := A
--     obtain ⟨fst_1, snd_1⟩ := B
--     simp_all only
--     sorry
--   assoc := by
--     intro A B C D f g h
--     funext z
--     obtain ⟨fst, snd⟩ := A
--     obtain ⟨fst_1, snd_1⟩ := B
--     obtain ⟨fst_2, snd_2⟩ := C
--     obtain ⟨fst_3, snd_3⟩ := D
--     simp_all only
--     sorry

-- theorem pushR_map
--   (f₀ : b' → Proxy a' a b' b m r)
--   (f : c' → Proxy b' b c' c m r)
--   (k : c → Proxy c' c b' b m r) :
--   Proxy.pushR k (f₀ +>> f) = f₀ +>> Proxy.pushR k f :=
--   by simp [pushR]; apply pushR_go'_map
--
-- theorem pushR_go'_map
--   (f₀ : b' → Proxy a' a b' b m r)
--   (f : c' → Proxy b' b c' c m r) :
--   ∀ (p : Proxy c' c b' b m r),
--     Proxy.pushR.go (λ c' => f₀ +>> f c') p = f₀ +>> Proxy.pushR.go f p := by
--   intro p
--   induction p with
--   | Pure x =>
--     simp [Proxy.pushR.go]
--   | Respond b' k ih =>
--     simp [Proxy.pushR.go]
--     ext
--     apply ih
--   | Request c k ih =>
--     simp [Proxy.pushR.go]
--     funext c'
--     exact ih c'
--   | M mx ih =>
--     simp [Proxy.pushR.go]
--     apply Functor.map_eq_map
--     exact ih
--
-- --------------------------------
--
-- -- First, let's prove the key distributivity lemma
-- theorem pushR_compose_distrib {a' c' c b' b : Type u} {m : Type u → Type u} {r : Type u}
--   (f : b' → Proxy a' a b' b m r)
--   (k : c → Proxy c' c b' b m r)
--   (p : Proxy b' b c' c m r) :
--   Proxy.pushR k (f +>> p) = f +>> Proxy.pushR k p := by
--   -- This is the key lemma your proof needs
--   induction p with
--   | Pure a => simp
--   | M mx => simp_all
--   | Respond b k' ih =>
--     simp_all
--     funext c'
--     exact ih c'
--   | Request x k' ih =>
--     simp_all
--     funext b
--     exact ih b
--
-- -- Now your main theorem becomes much simpler
-- theorem pushPullAssoc' {r c' c b : Type u} {m : Type u → Type u}
--   (f : b' → Proxy a' a b' b m r)
--   (g : a  → Proxy b' b c' c m r)
--   (h : c  → Proxy c' c b' b m r)
--   (xa : a) :
--   let gxa := g xa
--   ((f +>> gxa) >>~ h) = f +>> (gxa >>~ h) := by
--   simp only [Proxy.pullR]
--   -- Now we can use our distributivity lemma
--   exact pushR_compose_distrib f h (g xa)
--
-- -- Alternative approach using a more general lemma
-- theorem pushR_pullR_assoc {a' c' c b' b : Type u} {m : Type u → Type u} {r : Type u}
--   (f : b' → Proxy a' a b' b m r)
--   (p : Proxy b' b c' c m r)
--   (h : c → Proxy c' c b' b m r) :
--   Proxy.pushR h (f +>> p) = f +>> Proxy.pushR h p := by
--   -- This is essentially the same as pushR_compose_distrib
--   sorry -- Proof by induction on p, similar to above
--
-- -- Your theorem using the alternative lemma
-- theorem pushPullAssoc'_alt {r c' c b : Type u} {m : Type u → Type u}
--   (f : b' → Proxy a' a b' b m r)
--   (g : a  → Proxy b' b c' c m r)
--   (h : c  → Proxy c' c b' b m r)
--   (xa : a) :
--   let gxa := g xa
--   ((f +>> gxa) >>~ h) = f +>> (gxa >>~ h) := by
--   unfold Proxy.pullR
--   exact pushR_pullR_assoc f (g xa) h
--
-- -- If you need to handle the bind operation differently
-- theorem bind_pushR_distrib {a' c' c b' b : Type u} {m : Type u → Type u} {r : Type u}
--   (f : b' → Proxy a' a b' b m r)
--   (p : Proxy b' b c' c m r)
--   (k : c → Proxy c' c b' b m r) :
--   (p >>= fun x => Proxy.pushR k (f x)) = f +>> Proxy.pushR k p := by
--   -- This might be needed depending on your definitions
--   sorry
--
-- -- Pattern for nested inductions (if you must continue your original approach)
-- theorem nested_induction_helper {a' c' c b' b : Type u} {m : Type u → Type u} {r : Type u}
--   (f : b' → Proxy a' a b' b m r)
--   (k1 : c' → Proxy b' b c' c m r)
--   (k2 : c → Proxy c' c b' b m r) :
--   ∀ c', Proxy.pushR k2 (f +>> k1 c') = f +>> Proxy.pushR k2 (k1 c') := by
--   intro c'
--   exact pushR_compose_distrib f k2 (k1 c')

-- This helper eliminates the need for nested inductions in your original proof

--------------------------------
-- Complete proof of push-pull associativity using your exact definitions
-- (f >+> g) >~> h = f >+> (g >~> h)

--------------------------------
theorem pushPullAssoc' {r a' a c' c b b' : Type u}
  (f : b' → Proxy a' a b' b m r)
  (gxa : Proxy b' b c' c m r)
  (h : c  → Proxy c' c b' b m r) (xc' : c') :
  ((f +>> gxa) >>~ h) = f +>> (gxa >>~ h) := by
    induction gxa with -- 1
    | Pure a' => simp
    | M mx ih => simp_all
    | Respond b1 k1 ih1 =>
      specialize ih1 xc'
      rw [pullRespond]; dsimp
      induction k1 xc' with
      | Pure a'2 =>
        sorry
      | M mx2 ih2 Hih2 => sorry
      | Respond b2 k2 ih2 => sorry
      | Request x'2 k2 ih2 =>

      sorry
      -- induction h b1 with
      -- | Pure a'2 => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go]
      -- | M mx2 ih2 Hih2 => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go]
      -- | Respond b2 k2 ih2 => simp_all [Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go]
      -- | Request x'2 k2 ih2 =>
      --   simp_all [Proxy.pushR]
      --   induction k1 x'2 with -- 3
      --   | Pure a'3 => simp_all [Proxy.pushR]
      --   | M mx3 ih3 => simp_all [Proxy.pushR]
      --   | Respond b3 k3 ih3 =>
      --     rw [pullRespond]; dsimp
      --     sorry -- Proxy.pushR.go (fun a_1 => f +>> k3 a_1) (k2 b3) = f +>> Proxy.pushR.go k3 (k2 b3)
      --   | Request x'3 k3 ih3 =>
      --     simp_all [Proxy.rofP, Proxy.forP, Proxy.bind, Bind.bind, Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go]
      --     sorry
          /- theorem pushRequest -/
          /-   (f : b → Proxy b' b c' c m r) -/
          /-   (g : a → Proxy a' a b' b m r) -/
          /-   (x : a') : -/
          /-   Proxy.Request x g >>~ f = Proxy.Request x (g >~> f) := by -/
          /-     simp_all [Proxy.pushR] -/
          -- rw [pushRequest]
      -- sorry -- Proxy.pushR h (Proxy.Respond b fun a_1 => f +>> k a_1) = f +>> Proxy.pushR h (Proxy.Respond b k)
      -- rw [pullRespond]
      -- induction h b with -- 3
      -- | Pure a' => simp
      -- | M mx ih => simp_all
      -- | Respond b k ih => simp_all
      -- | Request x'2 k2 ih2 =>
      --   simp_all  -- 4
      --   induction k x'2 with -- 5
      --   | Pure a' => simp_all
      --   | M mx ih => simp_all
      --   | Respond b3 k3 ih3 =>
      --     simp_all -- 6
      --     induction k2 b3 with -- 7
      --     | Pure a' => simp
      --     | M mx ih => simp_all
      --     | Respond b4 k4 ih4 => simp_all
      --     | Request x'4 k4 ih4 =>
      --       simp_all -- 8
      --       induction k3 x'4 with -- 9
      --       | Pure a' => simp
      --       | M mx ih => simp_all
      --       | Respond b5 k5 ih5 =>
      --         simp_all -- 10
      --         induction k4 b5 with -- 11
      --         | Pure a' => simp_all
      --         | Request x'6 k'6 =>
      --           simp_all -- 12
      --           induction k5 x'6 with -- 12
      --           | Pure a' => simp_all
      --           | M m ih => simp_all
      --           | Request x'7 k'7 =>
      --             simp_all -- 13
      --             sorry -- 14
      --           | Respond y7 k'7 ih7 =>
      --             simp_all -- 15
      --             sorry -- 16
      --         | Respond y k' ih => simp_all
      --         | M m ih => simp_all
      --       | Request x'5 k5 ih5 =>
      --         simp_all [Proxy.rofP, Proxy.forP, Proxy.bind, Bind.bind, Proxy.pushR, Proxy.pushR.go, Proxy.pullR, Proxy.pullR.go]
      --         sorry
      --   | Request x'3 k3 ih3 =>
      --     simp_all [Proxy.rofP, Proxy.pushR, Proxy.pullR]
      --     sorry
    | Request x' k ih =>
      simp_all [Proxy.rofP, Proxy.pushR, Proxy.pullR]
      sorry

theorem pushPullAssoc [Monad m] [LawfulMonad m]
  (f : b' → Proxy a' a b' b m r)
  (g : a  → Proxy b' b c' c m r)
  (h : c  → Proxy c' c b' b m r) :
  (f >+> g) >~> h = f >+> (g >~> h) := by
  sorry

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
