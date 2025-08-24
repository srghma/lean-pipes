import Pipes.Core

/- module -/
/- public import all Pipes.Internal -/
/- public import all Pipes.Core -/

namespace PipesLawsCore

namespace ForLaws

theorem for_respond_f (f : b → Proxy x' x c' c m PUnit) (x_val : b) :
  Proxy.respond x_val //> f = f x_val := by
  simp_all [Proxy.respond]
  induction f x_val with
  | Pure a' => rfl
  | Respond b k ih =>
    simp_all
  | Request x' k ih =>
    simp_all
  | M mx ih =>
    simp_all

theorem for_respond (s : Proxy x' x PUnit b m PUnit) :
  s //> Proxy.respond = s := by
  induction s with
  | Pure a' => rfl
  | Respond b k ih =>
    simp_all [Proxy.forP]
  | Request x' k ih =>
    simp_all [Proxy.forP]
  | M mx ih =>
    simp_all [Proxy.forP]

theorem nested_for_a
  (s : Proxy x' x b' b m a')
  (f : b -> Proxy x' x c' c m b')
  (g : c -> Proxy x' x d' d m c') :
  -- Proxy.forP s (fun a => Proxy.forP (f a) g) = Proxy.forP (Proxy.forP s f) g := by
  (s //> (f />/ g)) = ((s //> f) //> g) := by
    induction s with
    | Pure a' => rfl
    | Respond b1 k1 ih1 =>
      simp_all
      induction f b1 with
      | Pure a' => rfl
      | Respond b2 k2 ih2 =>
        simp_all
        induction g b2 with
        | Pure a' => simp_all
        | Respond b2 k2 ih2 => simp_all
        | Request x' k ih => simp_all
        | M mx ih => simp_all
      | Request x' k ih => simp_all
      | M mx ih => simp_all
    | Request x' k ih => simp_all
    | M mx ih => simp_all

theorem nested_for_b
  (s : Proxy x' x b' b m a')
  (f : b -> Proxy x' x c' c m b')
  (g : c -> Proxy x' x d' d m c') :
  -- forP (Proxy.forP s f) g = Proxy.forP s (f />/ g) := by
  ((s //> f) //> g) = (s //> (f />/ g)) := by
  rw [nested_for_a]

end ForLaws

-- Respond Category
namespace RespondCategory

-- Respond distributivity theorem
theorem respondDistrib
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

theorem respondZero (someR : r) (f : c → Proxy a' a b' b m r): (Proxy.Pure />/ f) someR = Proxy.Pure someR := by rfl

end RespondCategory

namespace RequestCategory

theorem requestDistrib
  (f : c → Proxy b' b y' y m c')
  (g : c' → Proxy b' b y' y m r)
  (h : b' → Proxy a' a y' y m b) :
  h \>\ (f >=> g) = (h \>\ f) >=> (h \>\ g) := by
  funext x
  simp_all [Bind.kleisliRight, Bind.bind]
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

theorem requestZero (someR : r) (f : c → Proxy a' a b' b m r): (f \>\ Proxy.Pure) someR = Proxy.Pure someR := by rfl

end RequestCategory

theorem pushPullAssoc
  (f : b' → Proxy a' a b' b m r)
  (g : a  → Proxy b' b c' c m r)
  (h : c  → Proxy c' c b' b m r) :
  (f >+> g) >~> h = f >+> (g >~> h) := by
    dsimp
    funext arg
    induction g arg generalizing f h with
    | Pure r => simp [Proxy.pullR, Proxy.pushR]
    | M mx k ih => simp_all [Proxy.pushR, Proxy.pullR]
    | Request a k ih =>
      simp_all [Proxy.pushR, Proxy.pullR]
      induction f a generalizing k h with
      | Pure r => simp_all [Proxy.pushR, Proxy.pullR.go]
      | M mx k ih => simp_all [Proxy.pushR, Proxy.pullR.go]
      | Request a2 k2 ih2 => simp_all [Proxy.pushR, Proxy.pullR.go]
      | Respond x2 k2 ih2 => simp_all [Proxy.pullR.go]
    | Respond x k ih =>
      simp_all [Proxy.pushR, Proxy.pullR]
      induction h x generalizing k f with
      | Pure r => simp_all [Proxy.pushR.go, Proxy.pullR]
      | M mx k ih => simp_all [Proxy.pushR.go, Proxy.pullR]
      | Request a2 k2 ih2 => simp_all [Proxy.pushR.go]
      | Respond x2 k2 ih2 => simp_all [Proxy.pushR.go, Proxy.pullR]

namespace PushCategory

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

end PushCategory

namespace PullCategory

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
  | M mx k ih => simp_all
  | Request a k ih =>
    simp [Proxy.pullR]
    induction g a generalizing k h with
    | Pure r => simp [Proxy.pullR, Proxy.pullR.go]
    | M mx k ih2 => simp [Proxy.pullR.go, ih, ih2]
    | Respond x2 k2 ih2 => simp [Proxy.pullR.go, ih]
    | Request a2 k2 ih2 =>
      simp [Proxy.pullR, Proxy.pullR.go]
      induction h a2 generalizing k k2 with
      | Pure r => simp [Proxy.pullR.go]
      | M mx k ih3 => simp_all [Proxy.pullR.go]
      | Respond x3 k3 ih3 => simp_all [Proxy.pullR.go]
      | Request a3 k3 ih3 => simp_all [Proxy.pullR.go]
  | Respond x k ih => simp_all


end PullCategory

namespace Duals

theorem requestId : Proxy.reflect ∘ Proxy.request = @Proxy.respond a' a b' b m := by
  funext x
  simp [Proxy.reflect, Proxy.respond]

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
