import Aesop
-- import Mathlib.CategoryTheory.Category.Basic
import Pipes.Internal
import Canonical
import Mathlib.Data.Nat.Init

namespace Proxy

@[simp] def runEffect [Monad m] (eff : Proxy PEmpty a b' PEmpty m r) : m r :=
  match eff with
    | .Request x _ => PEmpty.elim x
    | .Respond x _ => PEmpty.elim x
    | .M mx k      => mx >>= fun x => runEffect (k x)
    | .Pure xr     => pure xr
  termination_by structural eff

@[inline, simp] def respond : b -> Proxy a' a b' b m b' := (Respond · Proxy.Pure)

@[simp] def forP
  (p0 :     Proxy x' x b' b m a')
  (fb : b → Proxy x' x c' c m b') :
            Proxy x' x c' c m a' :=
  match p0 with
  | .Request xa' k => .Request xa' (fun a => (k a).forP fb)
  | .Respond xb k => (fb xb).bind (fun b' => (k b').forP fb)
  | .M mx k => .M mx (fun x => (k x).forP fb)
  | .Pure xa' => .Pure xa'

infixl:60 " //> " => forP

infixl:60 " />/ " => fun f g a => f a //> g

-- Backward composition (request category)

@[inline, simp] abbrev request : a' -> Proxy a' a b' b m a := (Request · Proxy.Pure)

@[simp] def rofP
  (fb' : b' → Proxy a' a y' y m b)
  (p0 : Proxy b' b y' y m c) :
  Proxy a' a y' y m c :=
  match p0 with
  | .Request xb' k => (fb' xb').bind (fun b => (k b).rofP fb')
  | .Respond xy k => .Respond xy (fun y' => (k y').rofP fb')
  | .M mx k => .M mx (fun x => (k x).rofP fb')
  | .Pure xc => .Pure xc

infixl:60 " >\\\\ " => rofP

infixl:60 " \\>\\ " => fun f g a => f >\\ g a

def Fueled.push (default : r) : Nat -> a → Proxy a' a a' a m r
  | 0 => fun _ => .Pure default
  | n + 1 => (.Respond · (.Request · (Fueled.push default n)))

partial def Unbounded.push [Inhabited r] : a -> Proxy a' a a' a m r :=
  (.Respond · (.Request · Unbounded.push))

inductive ProxyPushRWF (a' a b' b c' c m r) where
  | go : (b' → Proxy a' a b' b m r) → Proxy b' b c' c m r → ProxyPushRWF a' a b' b c' c m r
  | reg : Proxy a' a b' b m r → ProxyPushRWF a' a b' b c' c m r

inductive ProxyPushRWFRel :
    ProxyPushRWF a' a b' b c' c m r → ProxyPushRWF a' a b' b c' c m r → Prop where
  | go_request : ProxyPushRWFRel (.reg (k xb')) (.go k (.Request xb' _kb))
  | go_respond : ProxyPushRWFRel (.go k (kc' yc)) (.go k (.Respond xc kc'))
  | go_m : ProxyPushRWFRel (.go k (kx x)) (.go k (.M mx kx))
  | request : ProxyPushRWFRel (.reg (k a)) (.reg (.Request xa' k))
  | m : ProxyPushRWFRel (.reg (k x)) (.reg (.M mx k))
  | respond : ProxyPushRWFRel (.go k t) (.reg (.Respond xb k))

instance : WellFoundedRelation (ProxyPushRWF a' a b' b c' c m r) where
  rel := ProxyPushRWFRel
  wf := by
    refine ⟨fun p => ?_⟩
    have H1 (x k) (hk : ∀ y, Acc ProxyPushRWFRel (.reg (k y) : ProxyPushRWF a' a b' b c' c m r)) :
        Acc ProxyPushRWFRel (.go k x : ProxyPushRWF a' a b' b c' c m r) := by
      induction x with
      | Request => exact ⟨_, fun | _, .go_request => hk _⟩
      | Respond _ _ ih => exact ⟨_, fun | _, .go_respond => ih _⟩
      | M _ _ ih => exact ⟨_, fun | _, .go_m => ih _⟩
      | Pure => exact ⟨_, nofun⟩
    have H2 (x) : Acc ProxyPushRWFRel (.reg x : ProxyPushRWF a' a b' b c' c m r) := by
      induction x with
      | Request _ _ ih => exact ⟨_, fun | _, .request => ih _⟩
      | Respond _ _ ih => exact ⟨_, fun | _, .respond => H1 _ _ ih⟩
      | M _ _ ih => exact ⟨_, fun | _, .m => ih _⟩
      | Pure => exact ⟨_, nofun⟩
    cases p with
    | reg => exact H2 _
    | go => exact H1 _ _ (fun _ => H2 _)

mutual
  def pushR.go'
    (fb' : b' → Proxy a' a b' b m r)
    (p : Proxy b' b c' c m r)
    : Proxy a' a c' c m r :=
    match p with
    | .Request xb' fb => pushR (fb' xb') fb
    | .Respond xc fc' => .Respond xc (fun c' => pushR.go' fb' (fc' c'))
    | .M mx kx => .M mx (fun x => pushR.go' fb' (kx x))
    | .Pure xr => .Pure xr
    termination_by ProxyPushRWF.go fb' p
    decreasing_by all_goals constructor

  def pushR
    (p0 : Proxy a' a b' b m r)
    (fb : b → Proxy b' b c' c m r) :
    Proxy a' a c' c m r :=
    match p0 with
    | .Request xa' k => .Request xa' (fun a => pushR (k a) fb)
    | .Respond xb fb' => pushR.go' fb' (fb xb)
    | .M t f => .M t (fun x => pushR (f x) fb)
    | .Pure xr => .Pure xr
    termination_by (.reg p0 : ProxyPushRWF a' a b' b c' c m r)
    decreasing_by all_goals constructor
end

infixl:60 " >>~ " => pushR

infixl:60 " >~> " => fun f g a => f a >>~ g

def Fueled.pull (default : r) : Nat -> a' → Proxy a' a a' a m r
  | 0 => fun _ => .Pure default
  | n + 1 => (.Request · (.Respond · (Fueled.pull default n)))

partial def Unbounded.pull [Inhabited r] : a' -> Proxy a' a a' a m r :=
  (.Request · (.Respond · Unbounded.pull))

inductive ProxyPullRWF (a' a b' b c' c m r) where
  | go : (b → Proxy b' b c' c m r) → Proxy a' a b' b m r → ProxyPullRWF a' a b' b c' c m r
  | reg : Proxy b' b c' c m r → ProxyPullRWF a' a b' b c' c m r

inductive ProxyPullRWFRel :
    ProxyPullRWF a' a b' b c' c m r → ProxyPullRWF a' a b' b c' c m r → Prop where
  | go_request : ProxyPullRWFRel (.go k (kc' yc)) (.go k (.Request xc kc'))
  | go_respond : ProxyPullRWFRel (.reg (k xb')) (.go k (.Respond xb' _kb))
  | go_m : ProxyPullRWFRel (.go k (kx x)) (.go k (.M mx kx))
  | request : ProxyPullRWFRel (.go k t) (.reg (.Request xb k))
  | respond : ProxyPullRWFRel (.reg (k a)) (.reg (.Respond xa' k))
  | m : ProxyPullRWFRel (.reg (k x)) (.reg (.M mx k))

instance : WellFoundedRelation (ProxyPullRWF a' a b' b c' c m r) where
  rel := ProxyPullRWFRel
  wf :=
    have H1 (x k) (hk : ∀ y, Acc ProxyPullRWFRel (.reg (k y) : ProxyPullRWF a' a b' b c' c m r)) :
        Acc ProxyPullRWFRel (.go k x : ProxyPullRWF a' a b' b c' c m r) := by
      induction x with
      | Respond => exact ⟨_, fun | _, .go_respond => hk _⟩
      | Request _ _ ih => exact ⟨_, fun | _, .go_request => ih _⟩
      | M _ _ ih => exact ⟨_, fun | _, .go_m => ih _⟩
      | Pure => exact ⟨_, nofun⟩
    have H2 (x) : Acc ProxyPullRWFRel (.reg x : ProxyPullRWF a' a b' b c' c m r) := by
      induction x with
      | Respond _ _ ih => exact ⟨_, fun | _, .respond => ih _⟩
      | Request _ _ ih => exact ⟨_, fun | _, .request => H1 _ _ ih⟩
      | M _ _ ih => exact ⟨_, fun | _, .m => ih _⟩
      | Pure => exact ⟨_, nofun⟩
    ⟨fun
      | .reg _ => H2 _
      | .go .. => H1 _ _ (fun _ => H2 _)⟩

mutual
  def pullR.go'
    (requestfb : b → Proxy b' b c' c m r)
    (p :         Proxy a' a b' b m r) :
                 Proxy a' a c' c m r :=
    match p with
    | .Request a' fa => .Request a' (fun a => pullR.go' requestfb (fa a))
    | .Respond b fb' => pullR fb' (requestfb b)
    | .M t f => .M t (fun x => pullR.go' requestfb (f x))
    | .Pure r => .Pure r
  termination_by ProxyPullRWF.go requestfb p
  decreasing_by all_goals constructor

  def pullR
    (fb' : b' → Proxy a' a b' b m r)
    (p0 :       Proxy b' b c' c m r) :
                Proxy a' a c' c m r :=
    match p0 with
    | .Request xb' fb => pullR.go' fb (fb' xb')
    | .Respond c fc' => .Respond c (fun c' => pullR fb' (fc' c'))
    | .M t f => .M t (fun x => pullR fb' (f x))
    | .Pure r => .Pure r
    termination_by (.reg p0 : ProxyPullRWF a' a b' b c' c m r)
    decreasing_by all_goals constructor
end

infixl:60 " +>> " => pullR

infixl:60 " >+> " => fun f g a => f +>> g a

-- Reflect operation (dual)
@[simp] def reflect (p : Proxy a' a b' b m r) : Proxy b b' a a' m r :=
  match p with
  | .Request xa' k => .Respond xa' (fun a => (k a).reflect)
  | .Respond xb k => .Request xb (fun b' => (k b').reflect)
  | .M mx k => .M mx (fun x => (k x).reflect)
  | .Pure xr => .Pure xr

notation:60 f " <\\\\ " g => g />/ f
notation:60 f " /</ " g => g \>\ f
notation:60 f " <~< " g => g >~> f
notation:60 f " <+< " g => g >+> f
notation:60 f " <// " x => x //> f
notation:60 x " //< " f => f >\\ x
notation:60 f " ~<< " x => x >>~ f
notation:60 x " <<+ " f => f +>> x

end Proxy

-- Type aliases
abbrev Effect      := Proxy PEmpty PUnit PUnit PEmpty
abbrev Producer b  := Proxy PEmpty PUnit PUnit b
abbrev Pipe a b    := Proxy PUnit a PUnit b -- downstream input -> downstream output
abbrev Consumer a  := Proxy PUnit a PUnit PEmpty
abbrev Client a' a := Proxy a' a PUnit PEmpty
abbrev Server b' b := Proxy PEmpty PUnit b' b

abbrev Effect_        m r := forall {a' a b' b}, Proxy a'   a b'   b m r
abbrev Producer_ b    m r := forall {a' a},      Proxy a'   a PUnit b m r
abbrev Consumer_ a    m r := forall {b' b},      Proxy PUnit a b'   b m r
abbrev Server_   b' b m r := forall {a' a},      Proxy a'   a b'   b m r
abbrev Client_   a' a m r := forall {b' b},      Proxy a'   a b'   b m r
