import Aesop
-- import Mathlib.CategoryTheory.Category.Basic
import Pipes.Internal
import Pipes.Core
import Canonical

namespace PipesLawsCore

universe u
variable (a' a b' b : Type u) (m : Type u -> Type u)

theorem pullR_go'_request
  (requestfb : b → Proxy b' b c' c m r)
  (x : a')
  (fa : a → Proxy a' a b' b m r) :
  Proxy.pullR.go' requestfb (Proxy.Request x fa) =
  Proxy.Request x (fun a => Proxy.pullR.go' requestfb (fa a)) := by simp

theorem pullR_go'_respond
  (fb : b → Proxy b' b c' c m r)
  (fb' : b' → Proxy a' a b' b m r)
  (xb : b) :
  Proxy.pullR.go' fb (Proxy.Respond xb fb') =
  Proxy.pullR fb' (fb xb) := by simp

-- For M case
theorem pullR_go'_m
  (fb : b → Proxy b' b c' c m r)
  (f : α → Proxy a' a b' b m r)
  (t : m α) :
  Proxy.pullR.go' fb (Proxy.M t f) =
  Proxy.M t (fun x => Proxy.pullR.go' fb (f x)) := by simp

-- For Pure case
theorem pullR_go'_pure
  (fb : b → Proxy b' b c' c m r)
  (r : r) :
  Proxy.pullR.go' (a' := a') (a := a) fb (Proxy.Pure r) =
  Proxy.Pure r := by simp

-- Theorems for main pullR function

-- For Request case (this connects pullR to pullR.go')
theorem pullR_request
  (fb' : b' → Proxy a' a b' b m r)
  (fb : b → Proxy b' b c' c m r)
  (xb' : b') :
  Proxy.pullR fb' (Proxy.Request xb' fb) =
  Proxy.pullR.go' fb (fb' xb') := by simp

-- For Respond case
theorem pullR_respond
  (fb' : b' → Proxy a' a b' b m r)
  (fc' : c' → Proxy b' b c' c m r)
  (xc : c) :
  Proxy.pullR fb' (Proxy.Respond xc fc') =
  Proxy.Respond xc (fun c' => Proxy.pullR fb' (fc' c')) := by simp

-- For M case
theorem pullR_m
  (fb' : b' → Proxy a' a b' b m r)
  (f : α → Proxy b' b c' c m r)
  (t : m α) :
  Proxy.pullR fb' (Proxy.M t f) =
  Proxy.M t (fun x => Proxy.pullR fb' (f x)) := by simp

-- For Pure case
theorem pullR_pure
  (fb' : b' → Proxy a' a b' b m r)
  (r : r) :
  Proxy.pullR (c' := c') (c := c) fb' (Proxy.Pure r) =
  Proxy.Pure r := by simp
