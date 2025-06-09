/-
- a' is the type of values flowing upstream (input)
- a  is the type of values flowing downstream (input)
- b' is the type of values flowing upstream (output)
- b  is the type of values flowing downstream (output)
- m  is the base monad
- r  is the return type
-/

import Aesop
import Init.Control.State
import Batteries.Control.AlternativeMonad
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

inductive Proxy.{u} (a' a b' b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
  | Request : a' → (a → Proxy a' a b' b m r) → Proxy a' a b' b m r
  | Respond : b → (b' → Proxy a' a b' b m r) → Proxy a' a b' b m r
  | M       {x : Type u} (op : m x) (cont : x → Proxy a' a b' b m r) : Proxy a' a b' b m r
  | Pure    : r → Proxy a' a b' b m r

instance [Inhabited r] : Inhabited (Proxy a' a b' b m r) where
  default := .Pure default


-- Fold function for the inductive type
@[inline] def foldProxy
  {s : Type v}
  (ka : a' → (a → s) → s)
  (kb : b → (b' → s) → s)
  (km : ∀ {x : Type u}, m x → (x → s) → s)
  (kp : r → s)
  (proxy : Proxy a' a b' b m r) : s :=
  match proxy with
  | .Request xa' k => ka xa' (fun a => foldProxy ka kb km kp (k a))
  | .Respond xb k => kb xb (fun b' => foldProxy ka kb km kp (k b'))
  | .M mx k => km mx (fun x => foldProxy ka kb km kp (k x))
  | .Pure xr => kp xr
  termination_by structural proxy

-- Bind operation
@[inline, simp] def Proxy.bind
  (p0 : Proxy a' a b' b m c)
  (f : c → Proxy a' a b' b m d) :
  Proxy a' a b' b m d :=
  match p0 with
  | .Request xa' k => .Request xa' (fun a => (k a).bind f)
  | .Respond xb k => .Respond xb (fun b' => (k b').bind f)
  | .M mx k => .M mx (fun x => (k x).bind f)
  | .Pure xc => f xc

@[inline, simp] def Proxy.map (f : r → s) (p : Proxy a' a b' b m r) : Proxy a' a b' b m s :=
  Proxy.bind p (Proxy.Pure ∘ f)

@[inline, simp] def Proxy.seq (pf : Proxy a' a b' b m (r → s)) (px : Unit → Proxy a' a b' b m r) : Proxy a' a b' b m s :=
  Proxy.bind pf (fun f => Proxy.map f (px ()))

@[inline, simp] def Proxy.request (xa' : a') : Proxy a' a b' b m a :=
  Proxy.Request xa' Proxy.Pure

@[inline, simp] def Proxy.respond (xb : b) : Proxy a' a b' b m b' :=
  Proxy.Respond xb Proxy.Pure

@[inline, simp] def Proxy.monadLift (mx : m r) : Proxy a' a b' b m r :=
  Proxy.M mx Proxy.Pure

@[inline] instance : Functor (Proxy a' a b' b m) := { map := Proxy.map }
@[inline] instance : Pure (Proxy a' a b' b m) := ⟨Proxy.Pure⟩
@[inline] instance : Seq (Proxy a' a b' b m) := ⟨Proxy.seq⟩
@[inline] instance : Bind (Proxy a' a b' b m) := ⟨Proxy.bind⟩
@[inline] instance : Monad (Proxy a' a b' b m) where
@[inline] instance : MonadLift m (Proxy a' a b' b m) := ⟨Proxy.monadLift⟩

instance : LawfulMonad (Proxy a' a b' b m) := LawfulMonad.mk'
  (id_map := by
    intro α x
    induction x with
    | Request a' k ih =>
      simp [Functor.map, Proxy.map]
      funext a
      exact ih a
    | Respond b k ih =>
      simp [Functor.map, Proxy.map]
      funext b'
      exact ih b'
    | M mx k ih =>
      simp [Functor.map, Proxy.map]
      funext x
      exact ih x
    | Pure r => rfl
  )
  (pure_bind := by intro α β x f; rfl)
  (bind_assoc := by
    intro α β γ x f g
    induction x with
    | Request a' k ih =>
      simp [Bind.bind, Proxy.bind]
      funext a
      exact ih a
    | Respond b k ih =>
      simp [Bind.bind, Proxy.bind]
      funext b'
      exact ih b'
    | M mx k ih =>
      simp [Bind.bind, Proxy.bind]
      funext x
      exact ih x
    | Pure r => rfl
  )

instance : LawfulApplicative (Proxy a' a b' b m) := inferInstance
instance : LawfulFunctor (Proxy a' a b' b m) := inferInstance

@[inline] instance [MonadState σ m] : MonadState σ (Proxy a' a b' b m) where
  get := Proxy.monadLift MonadState.get
  set := Proxy.monadLift ∘ MonadState.set
  modifyGet := Proxy.monadLift ∘ MonadState.modifyGet

@[inline] instance [MonadReader ρ m] : MonadReader ρ (Proxy a' a b' b m) where
  read := Proxy.M MonadReader.read Proxy.Pure

-- Type aliases
abbrev Effect      := Proxy Empty Unit Unit Empty
abbrev Producer b  := Proxy Empty Unit Unit b
abbrev Pipe a b    := Proxy Unit a Unit b -- downstream input -> downstream output
abbrev Consumer a  := Proxy Unit a Unit Empty
abbrev Client a' a := Proxy a' a Unit Empty
abbrev Server b' b := Proxy Empty Unit b' b

abbrev Effect_        m r := forall {a' a b' b}, Proxy a'   a b'   b m r
abbrev Producer_ b    m r := forall {a' a},      Proxy a'   a Unit b m r
abbrev Consumer_ a    m r := forall {b' b},      Proxy Unit a b'   b m r
abbrev Server_   b' b m r := forall {a' a},      Proxy a'   a b'   b m r
abbrev Client_   a' a m r := forall {b' b},      Proxy a'   a b'   b m r

@[always_inline, inline] def Proxy.runEffect [Monad m] (eff : Proxy Empty a b' Empty m r) : m r :=
  match eff with
    | .Request x _ => Empty.elim x
    | .Respond x _ => Empty.elim x
    | .M mx k      => mx >>= fun x => Proxy.runEffect (k x)
    | .Pure xr     => pure xr
  termination_by structural eff

-- Forward composition (respond category)
@[inline] def Proxy.forP
  (p0 : Proxy x' x b' b m a')
  (fb : b → Proxy x' x c' c m b') :
  Proxy x' x c' c m a' :=
  match p0 with
  | .Request xa' k => .Request xa' (fun a => (k a).forP fb)
  | .Respond xb k => (fb xb).bind (fun b' => (k b').forP fb)
  | .M mx k => .M mx (fun x => (k x).forP fb)
  | .Pure xa' => .Pure xa'

-- Backward composition (request category)
@[inline] def Proxy.rofP
  (fb' : b' → Proxy a' a y' y m b)
  (p0 : Proxy b' b y' y m c) :
  Proxy a' a y' y m c :=
  match p0 with
  | .Request xb' k => (fb' xb').bind (fun b => (k b).rofP fb')
  | .Respond xy k => .Respond xy (fun y' => (k y').rofP fb')
  | .M mx k => .M mx (fun x => (k x).rofP fb')
  | .Pure xc => .Pure xc

-- def Proxy.depth {a' a b' b : Type u} {m : Type u → Type u} {r : Type u} : Proxy a' a b' b m r → Nat
--   | .Request _ k => 1 + Finset.sup (Finset.range 1) (fun _ => 0) -- approximation since we can't enumerate all possible inputs
--   | .Respond _ k => 1 + Finset.sup (Finset.range 1) (fun _ => 0) -- same issue
--   | .M _ k => 1 + Finset.sup (Finset.range 1) (fun _ => 0) -- same issue
--   | .Pure _ => 0


-- Better approach: use structural termination with explicit proof
mutual
  def Proxy.pushR.go'_aux
    (fb : b → Proxy b' b c' c m r)
    (k : b' → Proxy a' a b' b m r)
    (p : Proxy b' b c' c m r)
    (h : sizeOf p < sizeOf p + 1) -- explicit proof that we're making progress
    :
    Proxy a' a c' c m r :=
    match p with
    | .Request xb' _kb =>
        have h1 : sizeOf (k xb') ≤ sizeOf (k xb') := by simp
        (k xb').pushR_aux fb (by simp;) 
    | .Respond xc kc' => .Respond xc (fun c' =>
        have h2 : sizeOf (kc' c') < sizeOf (kc' c') + 1 := by simp
        Proxy.pushR.go'_aux fb k (kc' c') h2)
    | .M mx kx => .M mx (fun x =>
        have h3 : sizeOf (kx x) < sizeOf (kx x) + 1 := by simp
        Proxy.pushR.go'_aux fb k (kx x) h3)
    | .Pure xr => .Pure xr
    termination_by sizeOf p

  def Proxy.pushR_aux
    (p0 : Proxy a' a b' b m r)
    (fb : b → Proxy b' b c' c m r)
    (h : sizeOf p0 < sizeOf p0 + 1)
    :
    Proxy a' a c' c m r :=
    match p0 with
    | .Request xa' k => .Request xa' (fun a =>
        have h1 : sizeOf (k a) < sizeOf (k a) + 1 := by simp
        (k a).pushR_aux fb h1)
    | .Respond xb k =>
        have h2 : sizeOf (fb xb) < sizeOf (fb xb) + 1 := by simp
        Proxy.pushR.go'_aux fb k (fb xb) h2
    | .M mx k => .M mx (fun x =>
        have h3 : sizeOf (k x) < sizeOf (k x) + 1 := by simp
        (k x).pushR_aux fb h3)
    | .Pure xr => .Pure xr
    termination_by sizeOf p0
end

mutual
  @[inline] partial def Proxy.pushR.go' [Inhabited r]
    (fb : b → Proxy b' b c' c m r)
    (k : b' → Proxy a' a b' b m r)
    (p : Proxy b' b c' c m r)
    :
    Proxy a' a c' c m r :=
    match p with
    | .Request xb' _kb => (k xb').pushR fb
    | .Respond xc kc' => .Respond xc (fun c' => Proxy.pushR.go' fb k (kc' c'))
    | .M mx kx => .M mx (fun x => Proxy.pushR.go' fb k (kx x))
    | .Pure xr => .Pure xr
    -- termination_by sizeOf p
    -- decreasing_by simp_wf; assumption

  -- Push category
  @[inline] partial def Proxy.pushR [Inhabited r]
    (p0 : Proxy a' a b' b m r)
    (fb : b → Proxy b' b c' c m r) :
    Proxy a' a c' c m r :=
    match p0 with
    | .Request xa' k => .Request xa' (fun a => (k a).pushR fb)
    | .Respond xb k => Proxy.pushR.go' fb k (fb xb)
    | .M mx k => .M mx (fun x => (k x).pushR fb)
    | .Pure xr => .Pure xr
    -- termination_by sizeOf p0
    -- decreasing_by simp_wf; sorry
end

-- -- We need to define a size function for termination
-- def Proxy.sizeOf : Proxy a' a b' b m r → Nat
--   | .Request _ k => 1 + sizeOf (k default)
--   | .Respond _ k => 1 + sizeOf (k default)
--   | .M _ k => 1 + sizeOf (k default)
--   | .Pure _ => 1

set_option trace.Elab.definition.body true
set_option pp.all true

-- def proxySize
--   [Inhabited a]
--   [Inhabited b]
--   [Inhabited a']
--   [Inhabited b']
--   [Inhabited c]
--   [Inhabited c']
--   [Inhabited x]
--   (p : Proxy a' a b' b m r) : Nat :=
--   match p with
--   | .Request _ f => 1 + proxySize (f default)
--   | .Respond _ f => 1 + proxySize (f default)
--   | .M _ f => 1 + proxySize (f default)
--   | .Pure _ => 0

mutual
  @[inline] def Proxy.pullR.go'
    [Nonempty (Proxy a' a c' c m r)]
    (fb' : b' → Proxy a' a b' b m r)
    (k : b → Proxy b' b c' c m r)
    (p : Proxy a' a b' b m r)
    :
    Proxy a' a c' c m r :=
    match p with
    | .Request xa' ka => .Request xa' (fun a => have kaa := ka a; Proxy.pullR.go' fb' k kaa)
    | .Respond xb _kb' => (k xb).pullR fb'
    | .M mx kx => .M mx (fun x => Proxy.pullR.go' fb' k (kx x))
    | .Pure xr => .Pure xr
    termination_by sizeOf p
    -- decreasing_by simp_wf; aesop?

  @[inline] def Proxy.pullR
    [Nonempty (Proxy a' a c' c m r)]
      (fb' : b' → Proxy a' a b' b m r)
    (p0 : Proxy b' b c' c m r) :
    Proxy a' a c' c m r :=
    match p0 with
    | .Request xb' k => Proxy.pullR.go' fb' k (fb' xb')
    | .Respond xc k => .Respond xc (fun c' => (k c').pullR fb')
    | .M mx k => .M mx (fun x => (k x).pullR fb')
    | .Pure xr => .Pure xr
    termination_by sizeOf p0
end

infixl:60 " //> " => Proxy.forP
infixl:60 " >\\\\ " => Proxy.rofP
infixl:60 " >>~ " => Proxy.pushR
infixl:60 " +>> " => Proxy.pullR

-- Function composition versions
def Proxy.forPFunc
  (f : a' → Proxy x' x b' b m a')
  (g : b → Proxy x' x c' c m b') :
  a' → Proxy x' x c' c m a' := fun a => f a //> g

def Proxy.rofPFunc
  (f : b' → Proxy a' a y' y m b)
  (g : c → Proxy b' b y' y m c) :
  c → Proxy a' a y' y m c := fun c => f >\\ g c

infixl:60 " />/ " => Proxy.forPFunc
infixl:60 " \\>\\ " => Proxy.rofPFunc

-- Utility functions
def Proxy.yield : b -> Producer b m Unit := Proxy.respond

def Proxy.await : Consumer a m a := Proxy.request ()

def Proxy.cat [Inhabited r] : Pipe a a m r :=
  .Request () (fun a => .Respond a (fun _ => Proxy.cat))

-- Convert list to producer
def Proxy.fromList : List a → Producer a m Unit
| []      => .Pure ()
| (x::xs) => .Respond x (fun _ => fromList xs)

-- Convert array to producer
def Proxy.fromArray : Array a -> Producer a m Unit :=
  fromList ∘ Array.toList

-- Filter pipe
def Proxy.filter [Inhabited r] (p : a -> Bool) : Pipe a a m r :=
  .Request () (fun a =>
    if p a then .Respond a (fun _ => Proxy.filter p)
    else Proxy.filter p)

-- Take n elements
def Proxy.take (n : Nat) : Pipe a a m Unit :=
  let rec go : Nat → Pipe a a m Unit
    | 0 => .Pure ()
    | n+1 => .Request () (fun a => .Respond a (fun _ => go n))
  go n

-- Drop n elements
def Proxy.drop (n : Nat) : Pipe a a m Unit :=
  let rec go : Nat → Pipe a a m Unit
    | 0 => Proxy.cat
    | n+1 => .Request () (fun _ => go n)
  go n

-- Enumerate with indices
def Proxy.enumerateGo [Inhabited r] (i : Nat) : Pipe a (Nat × a) m r :=
  .Request () (fun a => .Respond (i, a) (fun _ => Proxy.enumerateGo (i + 1)))

def Proxy.enumerate [Inhabited r] : Pipe a (Nat × a) m r := Proxy.enumerateGo 0

-- Map over a pipe
def Proxy.mapPipe (f : a → b) : Pipe a b m Unit :=
  .Request () (fun a => .Respond (f a) (fun _ => Proxy.mapPipe f))

def Proxy.scan [Inhabited r] (f : s → a → s) (acc : s) : Pipe a s m r :=
  .Request () (fun a =>
    let new_acc := f acc a
    .Respond new_acc (fun _ => Proxy.scan f new_acc))

-- For monadic effects
def Proxy.mapM [Inhabited r] (f : a -> m b) : Pipe a b m r :=
  .Request () (fun a => .M (f a) (fun b => .Respond b (fun _ => Proxy.mapM f)))

-- Print each element (for debugging)
def Proxy.print [ToString a] [MonadLift IO m] [Inhabited r] : Pipe a a m r :=
  .Request () (fun a =>
    .M (MonadLift.monadLift (IO.println (toString a))) (fun _ =>
      .Respond a (fun _ => Proxy.print)))

-- Reflect operation (dual)
def Proxy.reflect [Monad m] (p : Proxy a' a b' b m r) : Proxy b b' a a' m r :=
  match p with
  | .Request xa' k => .Respond xa' (fun a => (k a).reflect)
  | .Respond xb k => .Request xb (fun b' => (k b').reflect)
  | .M mx k => .M mx (fun x => (k x).reflect)
  | .Pure xr => .Pure xr

namespace Examples

-- Producer that creates numbers
def numbers : List Nat → Producer Nat m Unit := Proxy.fromList

-- Example: filter even numbers
def filterEven : Pipe Nat Nat m Unit := Proxy.filter (· % 2 = 0)

-- Example: take first 3
def takeThree : Pipe Nat Nat m Unit := Proxy.take 3

-- Example: add 10 to each number
def addTen : Pipe Nat Nat m Unit := Proxy.mapPipe (· + 10)

-- Example: enumerate
def enumerateNat : Pipe Nat (Nat × Nat) m Unit := Proxy.enumerate

-- Consumer that collects into a list
def toListConsumer [Inhabited a] : Consumer a (StateM (List a)) Unit :=
    .Request () (fun a =>
      .M (modify (fun acc => a :: acc)) (fun _ => toListConsumer))

-- Example pipeline
def examplePipeline : Producer String m Unit :=
  numbers [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    //> filterEven
    //> takeThree
    //> Proxy.mapPipe toString

end Examples

@[inline]
def Proxy.failure [Alternative m] : Proxy a' a b' b m r := Proxy.M Alternative.failure Proxy.Pure
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
--
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
--
--   #check Proxy.runEffect testAlt1 = .none
--   #check Proxy.runEffect testAlt2 = .some "world"
-- end AlternativeTest
