import Pipes.Internal
import Pipes.Core

namespace PipesLawsCore.PushGo

@[simp] theorem pushR_go'_respond
  (fb' : b' → Proxy a' a b' b m r)
  (fc' : c' → Proxy b' b c' c m r)
  (xc : c) :
  Proxy.pushR.go fb' (Proxy.Respond xc fc') =
  Proxy.Respond xc (fun c' => Proxy.pushR.go fb' (fc' c')) := by simp [Proxy.pushR.go]

@[simp] theorem pushR_go'_request
  (fb' : b' → Proxy a' a b' b m r)
  (fb : b → Proxy b' b c' c m r)
  (xb' : b') :
  Proxy.pushR.go fb' (Proxy.Request xb' fb) =
  Proxy.pushR (fb' xb') fb := by simp [Proxy.pushR.go]

@[simp] theorem pushR_go'_m
  (fb' : b' → Proxy a' a b' b m r)
  (f : α → Proxy b' b c' c m r)
  (t : m α) :
  Proxy.pushR.go fb' (Proxy.M t f) =
  Proxy.M t (fun x => Proxy.pushR.go fb' (f x)) := by simp [Proxy.pushR.go]

@[simp] theorem pushR_go'_pure
  (fb' : b' → Proxy a' a b' b m r)
  (r : r) :
  Proxy.pushR.go (c := c) (c' := c') fb' (Proxy.Pure r) =
  Proxy.Pure r := by simp [Proxy.pushR.go]

@[simp] theorem pushR_request
  (fb : b → Proxy b' b c' c m r)
  (k : a → Proxy a' a b' b m r)
  (xa' : a') :
  Proxy.pushR (Proxy.Request xa' k) fb =
  Proxy.Request xa' (fun a => Proxy.pushR (k a) fb) := by simp [Proxy.pushR, Proxy.pushR.go]

@[simp] theorem pushR_respond
  (fb : b → Proxy b' b c' c m r)
  (fb' : b' → Proxy a' a b' b m r)
  (xb : b) :
  Proxy.pushR (Proxy.Respond xb fb') fb =
  Proxy.pushR.go fb' (fb xb) := by simp [Proxy.pushR, Proxy.pushR.go]

@[simp] theorem pushR_m
  (fb : b → Proxy b' b c' c m r)
  (f : α → Proxy a' a b' b m r)
  (t : m α) :
  Proxy.pushR (Proxy.M t f) fb =
  Proxy.M t (fun x => Proxy.pushR (f x) fb) := by simp [Proxy.pushR, Proxy.pushR.go]

@[simp] theorem pushR_pure
  (fb : b → Proxy b' b c' c m r)
  (r : r) :
  Proxy.pushR (a := a) (a' := a') (Proxy.Pure r) fb =
  Proxy.Pure r := by simp [Proxy.pushR, Proxy.pushR.go]
