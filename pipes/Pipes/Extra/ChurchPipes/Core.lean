import Pipes.Extra.ChurchPipes.Internal

namespace CProxy

-- Run functions
abbrev CProxy.runEffect [Monad m] (eff : CProxy PEmpty a b' PEmpty m r) : m r :=
  eff
    (fun x _ => PEmpty.elim x) -- Handle Request (impossible)
    (fun x _ => PEmpty.elim x) -- Handle Respond (impossible)
    (fun _ f mt => mt >>= f)   -- Handle M
    pure                       -- Handle Pure

abbrev respond : b -> CProxy a' a b' b m b' := (Respond · Pure)

-- Forward composition (forP in Coq)
def forP
  (p0 : CProxy x' x b' b m a')
  (fb : b → CProxy x' x c' c m b') :
  CProxy x' x c' c m a' :=
  fun ka kb km kp =>
    p0 ka
      (fun b k => fb b ka kb km (fun b' => k b'))
      km
      kp

infixl:60 " //> " => forP

infixl:60 " />/ " => fun f g a => f a //> g

abbrev request : a' -> CProxy a' a b' b m a := (Request · Pure)

def rofP
  (fb' : b' → CProxy a' a y' y m b)
  (p0 : CProxy b' b y' y m c) :
  CProxy a' a y' y m c :=
  fun ka kb km kp =>
    p0
      (fun b' k => fb' b' ka kb km (fun b => k b))
      kb
      km
      kp

infixl:60 " >\\\\ " => rofP

infixl:60 " \\>\\ " => fun f g a => f >\\ g a

def Fueled.push {a a' m r} (default : r) : Nat -> a → CProxy a' a a' a m r
  | 0 => fun _ => Pure default
  | n + 1 => (Respond · (Request · (Fueled.push default n)))

partial def Unbounded.push {a a' r m} [Inhabited r] : a -> CProxy a' a a' a m r :=
  (Respond · (Request · Unbounded.push))

-- inductive CProxyPushRWF (a' a b' b c' c m r) where
--   | go : (b' → CProxy a' a b' b m r) → CProxy b' b c' c m r → CProxyPushRWF a' a b' b c' c m r
--   | reg : CProxy a' a b' b m r → CProxyPushRWF a' a b' b c' c m r
--
-- inductive CProxyPushRWFRel :
--     CProxyPushRWF a' a b' b c' c m r → CProxyPushRWF a' a b' b c' c m r → Prop where
--   | go_request : CProxyPushRWFRel (.reg (k xb')) (.go k (.Request xb' _kb))
--   | go_respond : CProxyPushRWFRel (.go k (kc' yc)) (.go k (.Respond xc kc'))
--   | go_m : CProxyPushRWFRel (.go k (kx x)) (.go k (.M mx kx))
--   | request : CProxyPushRWFRel (.reg (k a)) (.reg (.Request xa' k))
--   | m : CProxyPushRWFRel (.reg (k x)) (.reg (.M mx k))
--   | respond : CProxyPushRWFRel (.go k t) (.reg (.Respond xb k))
--
-- instance : WellFoundedRelation (CProxyPushRWF a' a b' b c' c m r) where
--   rel := CProxyPushRWFRel
--   wf := by
--     refine ⟨fun p => ?_⟩
--     have H1 (x k) (hk : ∀ y, Acc CProxyPushRWFRel (.reg (k y) : CProxyPushRWF a' a b' b c' c m r)) :
--         Acc CProxyPushRWFRel (.go k x : CProxyPushRWF a' a b' b c' c m r) := by
--       induction x with
--       | Request => exact ⟨_, fun | _, .go_request => hk _⟩
--       | Respond _ _ ih => exact ⟨_, fun | _, .go_respond => ih _⟩
--       | M _ _ ih => exact ⟨_, fun | _, .go_m => ih _⟩
--       | Pure => exact ⟨_, nofun⟩
--     have H2 (x) : Acc CProxyPushRWFRel (.reg x : CProxyPushRWF a' a b' b c' c m r) := by
--       induction x with
--       | Request _ _ ih => exact ⟨_, fun | _, .request => ih _⟩
--       | Respond _ _ ih => exact ⟨_, fun | _, .respond => H1 _ _ ih⟩
--       | M _ _ ih => exact ⟨_, fun | _, .m => ih _⟩
--       | Pure => exact ⟨_, nofun⟩
--     cases p with
--     | reg => exact H2 _
--     | go => exact H1 _ _ (fun _ => H2 _)

mutual
  def pushR.go
    (fb' : b' → CProxy a' a b' b m r)
    (p : CProxy b' b c' c m r)
    : CProxy a' a c' c m r :=
    fun ka kb km kp =>
    match p with
    | .Request xb' fb => pushR (fb' xb') fb
    | .Respond xc fc' => .Respond xc (fun c' => pushR.go fb' (fc' c'))
    | .M mx kx => .M mx (fun x => pushR.go fb' (kx x))
    | .Pure xr => .Pure xr
    termination_by CProxyPushRWF.go fb' p
    decreasing_by all_goals constructor

  def pushR
    (p0 : CProxy a' a b' b m r)
    (fb : b → CProxy b' b c' c m r) :
    CProxy a' a c' c m r :=
    match p0 with
    | .Request xa' k => .Request xa' (fun a => pushR (k a) fb)
    | .Respond xb fb' => pushR.go fb' (fb xb)
    | .M t f => .M t (fun x => pushR (f x) fb)
    | .Pure xr => .Pure xr
    termination_by (.reg p0 : CProxyPushRWF a' a b' b c' c m r)
    decreasing_by all_goals constructor
end

end CProxy

abbrev CEffect      := CProxy PEmpty PUnit PUnit PEmpty
abbrev CProducer b  := CProxy PEmpty PUnit PUnit b
abbrev CPipe a b    := CProxy PUnit a PUnit b -- downstream input -> downstream output
abbrev CConsumer a  := CProxy PUnit a PUnit PEmpty
abbrev CClient a' a := CProxy a' a PUnit PEmpty
abbrev CServer b' b := CProxy PEmpty PUnit b' b

abbrev CEffect_        m r := forall {a' a b' b}, CProxy a'   a b'   b m r
abbrev CProducer_ b    m r := forall {a' a},      CProxy a'   a PUnit b m r
abbrev CConsumer_ a    m r := forall {b' b},      CProxy PUnit a b'   b m r
abbrev CServer_   b' b m r := forall {a' a},      CProxy a'   a b'   b m r
abbrev CClient_   a' a m r := forall {b' b},      CProxy a'   a b'   b m r
