-- This module serves as the root of the `Pipes` library.
-- Import modules here that should be built as part of the library.
import Pipes.Core
import Pipes.Internal

import Aesop
import Init.Control.State
import Batteries.Control.AlternativeMonad
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

def Proxy.yield : b -> Producer b m Unit := Proxy.respond

infixl:70 " ~> " => fun f g => f />/ g
infixl:70 " <~ " => fun f g => g />/ f

notation:70 x " >~ " y => (fun (_ : Unit) => x) >\\ y
notation:70 x " ~< " y => y >~ x

def Proxy.await : Consumer a m a := Proxy.request ()

def Proxy.connect
  (p1 : Proxy a' a Unit b m r)
  (p2 : Proxy Unit b c' c m r) :
  Proxy a' a c' c m r :=
  (fun (_ : Unit) => p1) +>> p2

infixl:60 " >-> " => Proxy.connect
infixl:60 " <-< " => fun x y => Proxy.connect y x

@[inline]
def Proxy.next
  [_root_.Pure m] [Bind m]
  (p : Producer a m r) :
  m (Except r (a × (Unit → Producer a m r))) :=
  match p with
  | Proxy.Request v _  => False.elim v
  | Proxy.Respond a fu => pure (Except.ok (a, fun _ => fu ()))
  | Proxy.M mx k => mx >>= fun x => Proxy.next (k x)
  | Proxy.Pure r => pure (Except.error r)

@[inline] def Proxy.cat (default : r) (fuel : Nat) : Pipe a a m r := Proxy.pull default fuel ()

@[inline] def Proxy.cat_unbounded [Inhabited r] : Pipe a a m r := Proxy.pull_unbounded ()

@[inline] def Proxy.fromList : List a → Producer a m Unit
| []      => .Pure ()
| (x::xs) => .Respond x (fun _ => fromList xs)

@[inline] def Proxy.fromArray : Array a -> Producer a m Unit :=
  fromList ∘ Array.toList

@[inline] partial def Proxy.filter [Inhabited r] (p : a -> Bool) : Pipe a a m r :=
  .Request () (fun a =>
    if p a then .Respond a (fun _ => Proxy.filter p)
    else Proxy.filter p)

@[inline] def Proxy.take : Nat -> Pipe a a m Unit
  | 0 => .Pure ()
  | n+1 => .Request () (fun a => .Respond a (fun _ => Proxy.take n))

@[inline] def Proxy.drop_unbounded : Nat -> Pipe a a m Unit
  | 0 => Proxy.cat_unbounded
  | n+1 => .Request () (fun _ => Proxy.drop_unbounded n)

@[inline] partial def Proxy.enumerate.go [Inhabited r] (i : Nat) : Pipe a (Nat × a) m r :=
  .Request () (fun a => .Respond (i, a) (fun _ => go (i + 1)))

@[inline] def Proxy.enumerate [Inhabited r] : Pipe a (Nat × a) m r := Proxy.enumerate.go 0

@[inline] partial def Proxy.mapPipe (f : a → b) : Pipe a b m Unit :=
  .Request () (fun a => .Respond (f a) (fun _ => Proxy.mapPipe f))

@[inline] partial def Proxy.scan [Inhabited r] (f : s → a → s) (acc : s) : Pipe a s m r :=
  .Request () (fun a =>
    let new_acc := f acc a
    .Respond new_acc (fun _ => Proxy.scan f new_acc))

@[inline] partial def Proxy.mapM [Inhabited r] (f : a -> m b) : Pipe a b m r :=
  .Request () (fun a => .M (f a) (fun b => .Respond b (fun _ => Proxy.mapM f)))

@[inline] partial def Proxy.print [ToString a] [MonadLift IO m] [Inhabited r] : Pipe a a m r :=
  .Request () (fun a =>
    .M (MonadLift.monadLift (IO.println (toString a))) (fun _ =>
      .Respond a (fun _ => Proxy.print)))

namespace Examples

def triple [Monad m] (x : a) : Producer a m Unit := do
  Proxy.yield x
  Proxy.yield x
  Proxy.yield x

def numbers : List Nat → Producer Nat m Unit := Proxy.fromList

def filterEven : Pipe Nat Nat m Unit := Proxy.filter (· % 2 = 0)

def takeThree : Pipe Nat Nat m Unit := Proxy.take 3

def addTen : Pipe Nat Nat m Unit := Proxy.mapPipe (· + 10)

def enumerateNat : Pipe Nat (Nat × Nat) m Unit := Proxy.enumerate

partial def toListConsumer [Inhabited a] : Consumer a (StateM (List a)) Unit :=
  .Request () (fun a =>
    .M (modify (fun acc => a :: acc)) (fun _ => toListConsumer))

-- def examplePipeline : Producer String m Unit :=
--   numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
--     //> filterEven
--     //> takeThree
--     //> Proxy.mapPipe toString

end Examples

@[inline] def Proxy.failure [Alternative m] : Proxy a' a b' b m r := Proxy.M Alternative.failure Proxy.Pure

-- https://github.com/Gabriella439/pipes/commit/08e7302f43dbf2a40bd367c5ee73ee3367e17768
-- partial def Proxy.orElse [Monad m] [Alternative m]
--   (x : Proxy a' a b' b m ret) (y : Unit → Proxy a' a b' b m ret) : Proxy a' a b' b m ret :=
--   let rec convertToM : Proxy a' a b' b m ret → m ret
--     | .Request _ _ => Alternative.failure
--     | .Respond _ _ => Alternative.failure
--     | .M mx k => mx >>= (convertToM ∘ k)
--     | .Pure xr => pure xr
--   let rec go : Proxy a' a b' b m ret → Proxy a' a b' b m ret
--     | .Request xa' k => .Request xa' (fun a => go (k a))
--     | .Respond xb k => .Respond xb (fun b' => go (k b'))
--     | .M mx k => .M (Alternative.orElse mx (fun _ => convertToM (y ()))) (fun x => go (k x))
--     | .Pure xr => .Pure xr
--   go x
-- def Proxy.orElse [Monad m] [Alternative m]
--   (x : Proxy a' a b' b m r) (y : Unit → Proxy a' a b' b m r) : Proxy a' a b' b m r :=
--   match x with
--   | .Request a' k => .Request a' (fun a => Proxy.orElse (k a) y)
--   | .Respond b k => .Respond b (fun b' => Proxy.orElse (k b') y)
--   | .M mx k => .M (mx <|> do
--       let yx ← pure ()
--       let y' := y yx
--       match y' with
--       | .M my k' => ?my
--       | .Pure r => pure ?r
--       | _ => Alternative.failure) (fun x => Proxy.orElse (k x) y)
--   | .Pure r => .Pure r
-- @[inline] instance [Monad m] [Alternative m] : Alternative (Proxy a' a b' b m) := ⟨Proxy.failure, Proxy.orElse⟩
-- instance [Monad m] [Alternative m] [LawfulAlternative m] : LawfulAlternative (Proxy a' a b' b m) where
--   map_failure g := by sorry
--   failure_seq x := by sorry
--   map_orElse x y g := by rfl
--   orElse_failure x := by sorry
--   failure_orElse y := by sorry
--   orElse_assoc x y z := by sorry
-- namespace AlternativeTest
--   def testAlt1 : Proxy Empty Unit Unit Empty Option String := Proxy.failure
--   def testAlt2 : Proxy Empty Unit Unit Empty Option String := Proxy.Pure "world"
--   #check Proxy.runEffect testAlt1 = .none
--   #check Proxy.runEffect testAlt2 = .some "world"
-- end AlternativeTest
