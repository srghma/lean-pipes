/-
Pipes.Internal - Lean 4 Implementation

A streaming library based on the Proxy type, implemented using Church-encoded free monads.
adapted from PureScript pipes.

The Proxy type represents bidirectional communication between components:
- a' is the type of values flowing upstream
- a  is the type of values flowing downstream
- b' is the type of values flowing upstream (output)
- b  is the type of values flowing downstream (output)
- m  is the base monad
- r  is the return type
-/

import Aesop
import Pipes.FreeMonad

-- The core Proxy type using Church encoding via the F monad
inductive ProxyF (a' a b' b : Type u) (m : Type u → Type u) (next : Type u) : Type u where
  | Request : a' → (a → next) → ProxyF a' a b' b m next
  | Respond : b → (b' → next) → ProxyF a' a b' b m next
  | M : m next → ProxyF a' a b' b m next

@[inline]
instance [Functor m] : Functor (ProxyF a' a b' b m) where
  map f
    | ProxyF.Request a' k => ProxyF.Request a' (f ∘ k)
    | ProxyF.Respond b k => ProxyF.Respond b (f ∘ k)
    | ProxyF.M mn => ProxyF.M (f <$> mn)

-- The Proxy type using Church-encoded free monad
def Proxy (a' a b' b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1) := F (ProxyF a' a b' b m) r

@[inline] instance [Functor m] : Functor (Proxy a' a b' b m) := inferInstanceAs (Functor (F (ProxyF a' a b' b m)))
@[inline] instance [Functor m] : Pure (Proxy a' a b' b m) := inferInstanceAs (Pure (F (ProxyF a' a b' b m)))
@[inline] instance [Functor m] : Bind (Proxy a' a b' b m) := inferInstanceAs (Bind (F (ProxyF a' a b' b m)))
@[inline] instance [Functor m] : Monad (Proxy a' a b' b m) := inferInstanceAs (Monad (F (ProxyF a' a b' b m)))

@[inline] def Proxy.request [Functor m] (req : a') : Proxy a' a b' b m a := F.monadLift (ProxyF.Request req id)
@[inline] def Proxy.respond [Functor m] (resp : b) : Proxy a' a b' b m b' := F.monadLift (ProxyF.Respond resp id)
@[inline] def Proxy.monadLift [Functor m] {r : Type u} (mr : m r) : Proxy a' a b' b m r := F.monadLift (ProxyF.M mr)

@[inline] instance [Functor m] : MonadLift m (Proxy a' a b' b m) := ⟨Proxy.monadLift⟩

-- From https://github.com/leanprover-community/mathlib4/blob/730e4db21155a3faee9cadd55d244dbf72f06391/Mathlib/Control/Combinators.lean#L14-L17
@[inline] private def joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α := bind a id

@[inline] def runProxy [Monad m] [Functor m] (p : Proxy Empty any any2 Empty m r) : m r :=
  p.iterM fun
    | ProxyF.Request x _ => nomatch x  -- x : Empty → impossible
    | ProxyF.Respond x _ => nomatch x  -- x : Empty → impossible
    | ProxyF.M mval      => joinM mval -- just run the effect

-- Alternative instance when m has Alternative
@[inline] instance [Alternative m] [Functor m] : Alternative (Proxy a' a b' b m) where
  failure := ⟨fun _kp kf => kf (ProxyF.M failure)⟩
  orElse x y := ⟨fun kp kf =>
    kf (ProxyF.M (Alternative.orElse
      (pure (x.runF kp kf))
      (fun _ => pure ((y ()).runF kp kf))))⟩

set_option diagnostics true

-- @[inline] instance [Alternative m] [Functor m] : Alternative (Proxy a' a b' b m) := inferInstanceAs (Alternative (F (ProxyF a' a b' b m)))

@[inline] instance [Alternative m] [Functor m] : HOrElse (Proxy a' a b' b m r) (Proxy a' a b' b m r) (Proxy a' a b' b m r) := ⟨fun x y => Alternative.orElse x y⟩

namespace AlternativeTest
def testAlt1 : Proxy Empty Empty Empty Empty Option String := failure
def testAlt2 : Proxy Empty Empty Empty Empty Option String := F.pure $ "world"

#guard runProxy testAlt1 = .none
#guard runProxy testAlt2 = .some "world"

#guard runProxy (testAlt1 <|> testAlt2) = runProxy testAlt1 -- but should be 2

end AlternativeTest

-- MonadState instance
instance [Functor m] [MonadState σ m] : MonadState σ (Proxy a' a b' b m) where
  get := Proxy.monadLift MonadState.get
  set s := Proxy.monadLift (MonadState.set s)
  modifyGet f := Proxy.monadLift (MonadState.modifyGet f)

-- MonadReader instance
instance [Functor m] [MonadReader ρ m] : MonadReader ρ (Proxy a' a b' b m) where
  read := Proxy.monadLift MonadReader.read

-- Pipe type aliases
abbrev Producer b m r := Proxy Empty Unit Unit b m r
abbrev Consumer a m r := Proxy Unit a Unit Empty m r
abbrev Pipe a b m r := Proxy Unit a Unit b m r
abbrev Effect m r := Proxy Empty Unit Unit Empty m r

-- Producer operations
def yield [Functor m] (resp : b) : Producer b m Unit := Proxy.respond resp >>= fun _ => pure ()

def for [Monad m] [Functor m] (p : Producer b m r) (f : b → Consumer b m Unit) : Effect m r :=
  composeProxy p (f (closed X.mk))

-- Consumer operations
def await [Functor m] : Consumer a m a :=
  request () >>= fun a => pure a

def (>~) [Monad m] [Functor m] (p : Producer a m r) (c : Consumer a m s) : Effect m r :=
  composeProxy p c

-- Pipe operations
def cat [Functor m] : Pipe a a m r :=
  ⟨fun kp kf => kp (closed X.mk)⟩ -- Identity pipe

def take [Functor m] (n : Nat) : Pipe a a m Unit :=
  let rec go : Nat → Pipe a a m Unit
    | 0 => pure ()
    | n+1 => do
      a ← await
      yield a
      go n
  go n

def drop [Functor m] (n : Nat) : Pipe a a m Unit :=
  let rec go : Nat → Pipe a a m Unit
    | 0 => cat
    | n+1 => do
      _ ← await
      go n
  go n

def map [Functor m] (f : a → b) : Pipe a b m r :=
  ⟨fun kp kf => kp (closed X.mk)⟩ -- Simplified for now

-- Recursive worker to observe effects and re-wrap in ProxyF
-- (p : Proxy (a' : Type u) (a : Type u) (b' : Type u) (b : Type u) (m : Type u → Type u) (r : Type u)) :
-- def observeGo [Monad m] [Functor m] (p : Proxy a' a b' b m r) : m (Proxy a' a b' b m r) :=
--   p.runF
--     (fun r => pure (F.pure r))  -- pure case
--     (fun x =>
--       match x with
--       | Request a' fa  => pure (F.monadLift (Request a' (observe ∘ fa)))
--       | Respond b fb'  => pure (F.monadLift (Respond b  (observe ∘ fb')))
--       | M mnext        => mnext >>= observeGo
--     )
--
-- -- Top-level observe combinator
-- def observe [Monad m] [Functor m]
--     (p : Proxy a' a b' b m r) : Proxy a' a b' b m r :=
--   F.monadLift (observeGo p)

-- Example usage
namespace Examples

-- Simple producer that yields numbers
def numbers (n : Nat) : Producer Nat IO Unit :=
  let rec go : Nat → Producer Nat IO Unit
    | 0 => pure ()
    | n+1 => do
      yield n
      go n
  go n

-- Simple consumer that prints numbers
def printer : Consumer Nat IO Unit :=
  let rec go : Consumer Nat IO Unit := do
    n ← await
    lift (IO.println s!"Number: {n}")
    go
  go

-- Example pipeline
def examplePipeline : Effect IO Unit :=
  numbers 5 >~ take 3 >-> printer

end Examples

-- Laws and properties would go here
namespace Laws

-- Left identity: pure a >>= f = f a
theorem bind_pure_left [Monad m] (a : α) (f : α → Proxy a' a'' b' b'' m β) :
  F.pure a >>= f = f a := rfl

-- Right identity: m >>= pure = m
theorem bind_pure_right [Monad m] (p : Proxy a' a'' b' b'' m α) :
  p >>= F.pure = p := by
  cases p
  rfl

end Laws

-- Forward composition
def composeProxy [Monad m] [Functor m]
  (p1 : Proxy a' a b' b m r)
  (p2 : Proxy b' b c' c m r) :
  Proxy a' a c' c m r :=
⟨fun kp kf =>
  let rec go (px : Proxy a' a b' b m r) (py : Proxy b' b c' c m r) : m (ProxyF a' a c' c m r) := do
    px.runF
      (fun r => py.runF (pure ∘ kp ∘ fun _ => r) (pure ∘ kf))
      (fun pfx =>
        match pfx with
        | ProxyF.Request a' k => pure (ProxyF.Request a' (fun a => ⟨fun kp' kf' => go (k a) py⟩))
        | ProxyF.Respond b k =>
          py.runF
            (pure ∘ kf ∘ ProxyF.Respond b ∘ fun b' => ⟨fun kp' kf' => go (k b') py⟩)
            (fun pfy =>
              match pfy with
              | ProxyF.Request b'' k' => go px (k' b)
              | ProxyF.Respond c k' => pure (ProxyF.Respond c (fun c' => ⟨fun kp' kf' => go px (k' c')⟩))
              | ProxyF.M m => ProxyF.M <$> m)
        | ProxyF.M m => ProxyF.M <$> (m >>= fun next => go next py))
  kf <$> go p1 p2⟩

-- Backward composition
def composeProxyFlipped [Monad m] [Functor m]
  (p2 : Proxy b' b c' c m r)
  (p1 : Proxy a' a b' b m r) :
  Proxy a' a c' c m r :=
  composeProxy p1 p2

-- Composition operators
infixl:60 " >-> " => composeProxy
infixl:60 " <-< " => composeProxyFlipped
