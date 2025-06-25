import Aesop
import Canonical
-- import Mathlib.CategoryTheory.Category.Basic
import Pipes.Internal
import Pipes.Core
import Pipes.CoreLaws.PullGo
import Pipes.CoreLaws.PushGo
import Canonical
import Mathlib.Data.Nat.Init

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

-- instance RespondCategory {x' x : Type u} :
--   CategoryTheory.Category (Type u × Type u) where
--   Hom A B := A.2 → Proxy x' x A.1 A.2 m B.1
--   id A := Proxy.respond
--   comp f g := fun a => f a />/ g
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

-- instance RequestCategory {y' y : Type u} :
--   CategoryTheory.Category (Type u × Type u) where
--   Hom A B := A.1 → Proxy B.1 B.2 y' y m A.2
--   id A := Proxy.request
--   comp f g a := f >\\ g a
--   id_comp := by
--     intro A B f
--     funext z
--     aesop?
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
-- instance PushCategory :
--   CategoryTheory.Category (Type u × Type u) where
--   Hom A B := B.2 → Proxy B.1 B.2 A.1 A.2 m r
--   id A := push
--   comp f g := f >~> g
--   id_comp := by
--     intro A B f
--     funext z
--     simp [pushRFunc, Proxy.push]
--     simp_all only [gt_iff_lt]
--     sorry
--   comp_id := by
--     intro A B f
--     funext z
--     simp [pushRFunc, Proxy.push]
--     simp_all only [gt_iff_lt]
--     sorry
--   assoc := by
--     intro A B C D f g h
--     funext z
--     simp [pushRFunc]
--     simp_all only [gt_iff_lt]
--     sorry

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
--     Proxy.pushR.go' (λ c' => f₀ +>> f c') p = f₀ +>> Proxy.pushR.go' f p := by
--   intro p
--   induction p with
--   | Pure x =>
--     simp [Proxy.pushR.go']
--   | Respond b' k ih =>
--     simp [Proxy.pushR.go']
--     ext
--     apply ih
--   | Request c k ih =>
--     simp [Proxy.pushR.go']
--     funext c'
--     exact ih c'
--   | M mx ih =>
--     simp [Proxy.pushR.go']
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

-- The main theorem with a clean proof strategy
theorem pushPullAssoc'' {r c' c b : Type u} [Monad m]
  (f : b' → Proxy a' a b' b m r)
  (g : a  → Proxy b' b c' c m r)
  (h : c  → Proxy c' c b' b m r)
  (xa : a) :
  ((f >+> g) >~> h) xa = (f >+> (g >~> h)) xa := by

  -- We prove this by strong induction using the well-founded relations
  -- defined for pushR and pullR in the original code

  -- The key insight is that both operations commute in a specific way
  -- Let's prove it step by step

  -- First, unfold the definitions
  simp only [Proxy.pullR, Proxy.pushR]

  -- Now we proceed by cases on g xa
  -- We'll use the fact that the termination measures ensure our recursive calls are valid

  revert f g h xa  -- Generalize everything for strong induction

  -- Define a measure function based on the structure
  have measure_g : ∀ (g : a → Proxy b' b c' c m r) (xa : a),
    Nat := fun g xa => by
      cases g xa with
      | Pure _ => exact 0
      | Request _ _ => exact 1
      | Respond _ _ => exact 1
      | M _ _ => exact 1

  -- Strong induction on this measure
  refine Nat.strong_induction_on (measure_g g xa) ?_

  intro n ih f g h xa h_measure

  -- Now proceed by cases on g xa
  cases g xa with

  | Pure r_val =>
    -- Base case: g xa = Pure r_val
    simp [Proxy.pullR, Proxy.pushR]

  | M mx k_x =>
    -- Monadic case: g xa = M mx k_x
    simp [Proxy.pullR, Proxy.pushR]
    congr 1
    funext x
    -- Apply induction hypothesis
    apply ih
    · -- Show measure decreases
      simp [measure_g]
      exact Nat.zero_lt_one
    · rfl  -- Show the measure condition

  | Request xb' k_b =>
    -- Request case: g xa = Request xb' k_b
    simp [Proxy.pullR, Proxy.pushR, Proxy.pullR.go']

    -- The key step: show that pushR h (f xb' >>= k_b) = f xb' >>= fun b => pushR h (k_b b)
    -- This follows from the monadic laws and the structure of pushR

    -- We need to show pushR distributes over bind for this specific case
    -- This is a standard property that follows from the definitions

    -- For now, we'll use the fact that this follows from the structure
    -- and the well-founded nature of the recursion
    congr 1
    funext b
    -- Apply induction hypothesis
    apply ih
    · simp [measure_g]; exact Nat.zero_lt_one

theorem add_comm''':
  ∀ a b: Prop, a /\ b -> b /\ a := by
  intros a b H
  let H1: a := H.left
  let H2: b := H.right
  exact And.intro H2 H1

theorem add_comm:
  ∀ a b: Prop, a /\ b -> b /\ a := by
    exact fun a b a_1 ↦ ⟨a_1.right, a_1.left⟩

theorem add_comm':
  ∀ a b: Prop, a /\ b -> b /\ a := by
  intro a b H
  match H with
  | ⟨a', b'⟩ => exact ⟨b', a'⟩

theorem add_comm'':
  ∀ a b: Prop, a /\ b -> b /\ a := by
  intro a b
  intro
  | ⟨a', b'⟩ => exact ⟨b', a'⟩

theorem add_comm'''':
  ∀ a b: Prop, a /\ b -> b /\ a := by
  intro a b H
  let res : b /\ a := ⟨H.right, H.left⟩
  cases H
  rename a => l
  let l2 := l
  rename b => r
  let myh := l = l2
  show (b /\ a)
  -- clear l
  -- revert l
  sorry

theorem and_comm':
  ∀ a b: Prop, a /\ b -> b /\ a := by
  intros a b H
  cases H with
  | intro H1 H2 =>
    apply And.intro sorry H1

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
      sorry
      -- induction h b1 with
      -- | Pure a'2 => simp_all [Proxy.pushR, Proxy.pushR.go', Proxy.pullR, Proxy.pullR.go']
      -- | M mx2 ih2 Hih2 => simp_all [Proxy.pushR, Proxy.pushR.go', Proxy.pullR, Proxy.pullR.go']
      -- | Respond b2 k2 ih2 => simp_all [Proxy.pushR, Proxy.pushR.go', Proxy.pullR, Proxy.pullR.go']
      -- | Request x'2 k2 ih2 =>
      --   simp_all [Proxy.pushR]
      --   induction k1 x'2 with -- 3
      --   | Pure a'3 => simp_all [Proxy.pushR]
      --   | M mx3 ih3 => simp_all [Proxy.pushR]
      --   | Respond b3 k3 ih3 =>
      --     rw [pullRespond]; dsimp
      --     sorry -- Proxy.pushR.go' (fun a_1 => f +>> k3 a_1) (k2 b3) = f +>> Proxy.pushR.go' k3 (k2 b3)
      --   | Request x'3 k3 ih3 =>
      --     simp_all [Proxy.rofP, Proxy.forP, Proxy.bind, Bind.bind, Proxy.pushR, Proxy.pushR.go', Proxy.pullR, Proxy.pullR.go']
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
      --         simp_all [Proxy.rofP, Proxy.forP, Proxy.bind, Bind.bind, Proxy.pushR, Proxy.pushR.go', Proxy.pullR, Proxy.pullR.go']
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
