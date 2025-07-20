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

-- mutual
--   def pushR.go
--     (fb' : b' → CProxy a' a b' b m r)
--     (p : CProxy b' b c' c m r)
--     : CProxy a' a c' c m r :=
--     fun {s} ka kb km kp =>
--       p
--         -- Handle Request from p: b' → (b → s) → s
--         (fun xb' k_b_to_s =>
--           -- We need to call pushR on (fb' xb') with the continuation k_b_to_s
--           -- But k_b_to_s expects a b, so we need to adapt it
--           pushR (fb' xb') (fun b =>
--             -- Convert the b to the expected CProxy b' b c' c m r
--             fun ka' kb' km' kp' => k_b_to_s b) ka kb km kp)

--         -- Handle Respond from p: c → (c' → s) → s
--         (fun xc k_c'_to_s =>
--           -- Respond with xc, and for continuation, apply pushR.go recursively
--           kb xc (fun c' =>
--             pushR.go fb' (fun ka' kb' km' kp' => k_c'_to_s c') ka kb km kp))

--         -- Handle M from p: ∀ x, (x → s) → m x → s
--         (fun x k_x_to_s mx =>
--           km x (fun x_val =>
--             pushR.go fb' (fun ka' kb' km' kp' => k_x_to_s x_val) ka kb km kp) mx)

--         -- Handle Pure from p: r → s
--         (fun xr => kp xr)

--   def pushR
--     (p0 : CProxy a' a b' b m r)
--     (fb : b → CProxy b' b c' c m r) :
--     CProxy a' a c' c m r :=
--     fun {s} ka kb km kp =>
--       p0
--         -- Handle Request from p0: a' → (a → s) → s
--         (fun xa' k_a_to_s =>
--           ka xa' (fun a =>
--             pushR (fun {s2} ka' kb' km' kp' => k_a_to_s a) fb ka kb km kp))

--         -- Handle Respond from p0: b → (b' → s) → s
--         (fun xb k_b'_to_s =>
--           -- This is where we connect to fb
--           pushR.go (fun b' =>
--             fun ka' kb' km' kp' => k_b'_to_s b') (fb xb) ka kb km kp)

--         -- Handle M from p0: ∀ x, (x → s) → m x → s
--         (fun x k_x_to_s mx =>
--           km x (fun x_val =>
--             pushR (fun ka' kb' km' kp' => k_x_to_s x_val) fb ka kb km kp) mx)

--         -- Handle Pure from p0: r → s
--         (fun xr => kp xr)
-- end

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
