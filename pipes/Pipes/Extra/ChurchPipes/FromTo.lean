import Pipes.Extra.ChurchPipes.Internal
import Pipes.Internal
/- import Canonical -/
/- import Aesop -/

open CProxy

namespace CProxy

-- Convert Church-encoded CProxy into inductive Proxy
def toProxy (p : CProxy.{u} a' a b' b m r) : Proxy.{u} a' a b' b m r :=
  p (Proxy.{u} a' a b' b m r)
  Proxy.Request
  Proxy.Respond
  (fun _ k mx => Proxy.M mx k)
  Proxy.Pure

-- Convert inductive Proxy into Church-encoded CProxy
def fromProxy (p : Proxy.{u} a' a b' b m r) : CProxy.{u} a' a b' b m r :=
  match p with
  | .Request xa' k => CProxy.Request xa' (fun a => fromProxy (k a))
  | .Respond xb k  => CProxy.Respond xb (fun b' => fromProxy (k b'))
  | .M mx k        => fun s ka kb km kp => km _ (fun x => fromProxy (k x) s ka kb km kp) mx
  | .Pure xr       => fun _s _ka _kb _km kp => kp xr

end CProxy

theorem to_from_id
  (p : Proxy a' a b' b m r) : toProxy (fromProxy p) = p := by
  induction p with
  | Request a' k ih =>
    simp [fromProxy, toProxy]
    ext x : 1
    apply ih
  | Respond b k ih =>
    simp [fromProxy, toProxy, Respond]
    ext x : 1
    apply ih
  | M x k ih =>
    simp [fromProxy, toProxy]
    ext x : 1
    apply ih
  | Pure r =>
    simp [fromProxy, toProxy]

/- https://github.com/jwiegley/coq-pipes/blob/ec4e7884dc2d2c1a55ee075103c964b4f65c7be6/src/Pipes/Extras.v#L58 -/

-- Key insight from Coq: Parametricity axiom for Church encodings
-- This says that any Church-encoded value, when applied to pure constructor,
-- must equal the result of applying the Church encoding to all constructors
/-
axiom church_parametricity (sp : CProxy a' a b' b m r) (s : Type)
  (req : a' → (a → s) → s)
  (res : b → (b' → s) → s)
  (mon : ∀ x, (x → s) → m x → s)
  (pur : r → s) (z : r) :
  pur z = sp s req res mon pur

axiom f_const {α β γ : Type} (f : α → (β → γ) → γ) (x : α) (y : γ) :
  f x (fun _ => y) = y

theorem from_to_id (p : CProxy.{u} a' a b' b m r) : fromProxy (toProxy p) = p := by
  funext s ka kb km kp
  simp_all [toProxy]
  simp_all [church_parametricity, f_const]
-/
