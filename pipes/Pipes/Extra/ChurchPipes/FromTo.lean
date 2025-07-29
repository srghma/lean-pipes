import Pipes.Extra.ChurchPipes.Internal
import Pipes.Internal

open CProxy

namespace CProxy

-- Convert Church-encoded CProxy into inductive Proxy
def toProxy  (p : CProxy.{u} a' a b' b m r) : Proxy.{u} a' a b' b m r :=
  p _
  (fun a' k => Proxy.Request a' (fun a => k a))
  (fun b  k => Proxy.Respond b  (fun b' => k b'))
  (fun _ k mx => Proxy.M mx (fun x => k x))
  Proxy.Pure

-- Convert inductive Proxy into Church-encoded CProxy
def fromProxy (p : Proxy a' a b' b m r) : CProxy a' a b' b m r :=
  match p with
  /- | .Request xa' k => CProxy.Request xa' (fun a => fromProxy (k a)) -/
  /- | .Respond xb k  => CProxy.Respond xb  (fun b' => fromProxy (k b')) -/
  | .Request xa' k => fun s ka kb km kp => ka xa' (fun xa => fromProxy (k xa) s ka kb km kp)
  | .Respond xb k  => fun s ka kb km kp => kb xb (fun b' => fromProxy (k b') s ka kb km kp)
  | .M mx k        => fun s ka kb km kp => km _ (fun x => fromProxy (k x) s ka kb km kp) mx
  | .Pure xr       => fun _s _ka _kb _km kp => kp xr

end CProxy
