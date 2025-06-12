-- This module serves as the root of the `Pipes` library.
-- Import modules here that should be built as part of the library.
import Pipes.Core
import Pipes.Internal

import Aesop
import Init.Control.State
import Batteries.Control.AlternativeMonad
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

namespace Proxy

-- implementation is same as `respond`, but cannot use `:= respond`
-- @[inline, simp] abbrev yield : b -> Producer_ b m PUnit := (Respond · Proxy.Pure)
@[inline, simp] abbrev yield : b -> Proxy a' a PUnit b m PUnit := respond

infixl:70 " ~> " => fun f g => f />/ g
infixl:70 " <~ " => fun f g => g />/ f

notation:70 x " >~ " y => (fun (_ : PUnit) => x) >\\ y
notation:70 x " ~< " y => y >~ x

-- @[inline, simp] abbrev await : Consumer_ a m a := request ()
@[inline, simp] abbrev await : Proxy PUnit a b' b m a := request ()

@[inline] def Fueled.cat (default : r) (fuel : Nat) : Pipe a a m r := Fueled.pull default fuel ()

@[inline] def Unbounded.cat [Inhabited r] : Pipe a a m r := Unbounded.pull ()

def connect [Inhabited r] -- TODO: prove termination of pullR and pushR
  (p1 : Proxy a' a PUnit b m r)
  (p2 : Proxy PUnit b c' c m r) :
  Proxy a' a c' c m r :=
  (fun (_ : PUnit) => p1) +>> p2

infixl:60 " >-> " => connect
infixl:60 " <-< " => fun x y => connect y x

-- --- DISALLOWED NEXT
-- @[inline]
-- def next
--   [_root_.Pure m] [Bind m]
--   (p : Producer b m r) :
--   m (r ⊕ (a × (Producer b m r))) :=
--   match p with
--   | Request v _  => PEmpty.elim v
--   | Respond a fu => pure (Sum.inr (a, fun _ => fu ()))
--   | M mx k => mx >>= fun x => Proxy.next (k x)
--   | Pure r => pure (Sum.inl r)
-- --- IDEA 1 : ProxyNextStep is just Proxy with disabled fields
-- inductive ProxyNextStep.{u} (b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
--   | Respond : b → (Unit → ProxyNextStep b m r) → ProxyNextStep b m r
--   | M {x : Type u} (op : m x) (cont : x → ProxyNextStep b m r) : ProxyNextStep b m r
--   | Pure    : r → ProxyNextStep b m r
-- def ProxyNextStep.fromProducer [Monad m] (p : Producer b m r) : ProxyNextStep b m r :=
--   match p with
--   | Request v _    => PEmpty.elim v
--   | Respond b fu   => (ProxyNextStep.Respond b (fun _ => ProxyNextStep.fromProducer (fu ())))
--   | M op cont      => (ProxyNextStep.M op ((fun x => ProxyNextStep.fromProducer (cont x))))
--   | Pure r         => (ProxyNextStep.Pure r)
---- IDEA 2 : ProxyNextStep is more complex (this idea is most clean)
inductive ProxyNextStep.{u} (b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
  | Respond {x : Type u} (downstreamOutput : Option b) (op : m x) (cont : x → ProxyNextStep b m r) : ProxyNextStep b m r
  | Pure    : r → ProxyNextStep b m r
def next [Monad m] (p : Producer b m r) : ProxyNextStep b m r :=
  match p with
  | Request v _ => PEmpty.elim v
  | Respond b fu => ProxyNextStep.Respond (.some b) (pure ()) (fun _ => Proxy.next (fu ()))
  | M op cont => ProxyNextStep.Respond .none op (fun x => Proxy.next (cont x))
  | Pure r => ProxyNextStep.Pure r
  termination_by structural p
---- IDEA 3 : Can move downstreamOutput to m? yes
-- inductive ProxyNextStep.{u} (b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
--   | Respond {x : Type u} (op : m (Option b × x)) (cont : x → ProxyNextStep b m r) : ProxyNextStep b m r
--   | Pure    : r → ProxyNextStep b m r
-- def next [Monad m] (p : Producer b m r) : ProxyNextStep b m r :=
--   match p with
--   | Request v _ => PEmpty.elim v
--   | Respond b fu =>
--     ProxyNextStep.Respond (pure (some b, ())) (fun _ => next (fu ()))
--   | M op cont =>
--     ProxyNextStep.Respond (do
--       pure (none, (← op))
--     ) (fun x => next (cont x))
--   | Pure r => ProxyNextStep.Pure r
--   termination_by structural p
---- IDEA 4 : can I purge Option?
-- inductive ProxyNextStep.{u} (b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
--   | Respond {x : Type u} (downstreamOutput : b) (op : m x) (cont : x → ProxyNextStep b m r) : ProxyNextStep b m r
--   | Pure    : r → ProxyNextStep b m r
------- A: no
---- IDEA 5 : can I purge m?
-- inductive ProxyNextStep.{u} (b : Type u) (r : Type u) : Type u
-- | Respond {x : Type u} (op : (Option b × x)) (cont : x → ProxyNextStep b r) : ProxyNextStep b r
-- | Pure    : r → ProxyNextStep b r
------- A: no, x doesnt allow

-- each = every, in coq too
@[inline] def each (xs : List b) : Producer b m PUnit :=
  xs.forM respond

@[inline] def every (xs : List b) : Producer b m PUnit :=
  xs.foldlM (fun _ x => respond x) ()

namespace PipesForLaws
theorem for_yield_f (f : b → Proxy x' x c' c m PUnit) (x_val : b) :
  yield x_val //> f = f x_val := by
  simp only [forP, Proxy.yield, Proxy.respond]
  sorry

theorem for_yield (s : Proxy x' x PUnit b m PUnit) :
  s //> yield = s := by
  simp only [Proxy.forP, Proxy.yield, Proxy.respond]
  sorry

theorem nested_for_a
  (s : Proxy x' x b' b m a')
  (f : b -> Proxy x' x c' c m b')
  (g : c -> Proxy x' x d' d m c') :
  -- forP s (fun a => Proxy.forP (f a) g) = Proxy.forP (Proxy.forP s f) g := by
  (s //> (f />/ g)) = ((s //> f) //> g) := by
  sorry

theorem nested_for_b
  (s : Proxy x' x b' b m a')
  (f : b -> Proxy x' x c' c m b')
  (g : c -> Proxy x' x d' d m c') :
  -- forP (Proxy.forP s f) g = Proxy.forP s (f />/ g) := by
  ((s //> f) //> g) = (s //> (f />/ g)) := by
  rw [nested_for_a]

end PipesForLaws

--------------------------

-- Definition repeatM `{Monad m} `(x : m a) : Producer' a m r :=
--   fun _ _ => lift x >~ cat (n:=n) (d:=d).
--
-- replicateM :: Monad m => Int -> m a -> Producer' a m ()
-- replicateM n m = lift m >~ take n

@[inline] def Fueled.drain (d : r) (fuel : Nat) : Consumer_ a m r :=
  -- forP (Proxy.Fueled.cat d fuel) (fun _ => Proxy.Pure ())
  match fuel with
  | 0     => .Pure d
  | fuel' + 1 => .Request .unit (fun _ => Fueled.drain d fuel')

@[inline] partial def Unbounded.drain [Inhabited r] : Consumer_ a m r :=
  -- forP (Proxy.Unbounded.cat) (fun _ => Proxy.Pure ())
  .Request .unit (fun _ => drain)

-- In coq - just `map`, bad name
@[inline] def Fueled.mapPipe (d : r) (fuel : Nat) (f : a → b) : Pipe a b m r :=
  -- forP (Proxy.Fueled.cat d fuel) (fun val => Proxy.respond (f val))
  match fuel with
  | 0     => .Pure d
  | fuel' + 1 => .Request .unit (fun a => .Respond (f a) (fun _ => Fueled.mapPipe d fuel' f))

@[inline] partial def Unbounded.mapPipe [Inhabited r] (f : a → b) : Pipe a b m r :=
  forP (Proxy.Unbounded.cat) (fun val => Proxy.respond (f val))
  -- .Request () (fun a => .Respond (f a) (fun _ => mapPipe f))

-- In coq - just `mapM`, bad name
@[inline] def Pipe.Fueled.mapM [Monad m] (f : a → m b) (d : r) (fuel : Nat) : Pipe a b m r :=
  if fuel == 0 then
    .Pure d
  else
    .Request .unit fun a =>
      .M (f a) fun b =>
        .Respond b fun _ =>
          mapM f d (fuel - 1)
  decreasing_by
    apply Nat.sub_lt
    · exact Nat.zero_lt_of_ne_zero (by intro h; simp_all [beq_iff_eq];)
    · exact Nat.zero_lt_one

@[inline] partial def Pipe.Unbounded.mapM [Inhabited r] (f : a -> m b) : Pipe a b m r :=
  .Request () (fun a => .M (f a) (fun b => .Respond b (fun _ => mapM f)))

@[inline] def Fueled.mapM_ [Monad m] (f : a → m PUnit) (d : r) (fuel : Nat) : Consumer a m r :=
  forP (Proxy.Fueled.cat d fuel) (fun val => monadLift (f val))

@[inline] partial def Unbounded.mapM_ [Inhabited r] (f : a → m PUnit) : Consumer a m r :=
  forP Proxy.Unbounded.cat (fun val => monadLift (f val))
  -- .Request ?? (fun a => .M (f a) (fun _ => Unbounded.mapM_ f))

@[inline] def Pipe.Fueled.sequence [Monad m] (d : r) (fuel : Nat) : Pipe (m a) a m r :=
  mapM id d fuel

@[inline] partial def Pipe.Unbounded.sequence [Inhabited r] : Pipe (m a) a m r :=
  mapM id

@[inline] def Fueled.mapFoldable (d : r) (fuel : Nat) (f : a → List b) : Pipe a b m r :=
  forP (Proxy.Fueled.cat d fuel) (fun x => (f x).forM Proxy.respond)

@[inline] def whenP (cond : Bool) (action : Pipe a a m PUnit) : Pipe a a m PUnit :=
  if cond then action else Pure ()

-- NOTE: coq uses `forP` version
@[inline] def Fueled.ForPVersion.filter (d : r) (fuel : Nat) (p : a → Bool) : Pipe a a m r :=
  forP (Proxy.Fueled.cat d fuel) (fun x => whenP (p x) (Proxy.yield x))

@[inline] def Fueled.filter
  (d : r)
  (p : a → Bool)
  (fuel : Nat)
  : Pipe a a m r :=
    if fuel == 0 then
      Pure d
    else
      Request PUnit.unit fun a =>
        if p a then Respond a fun _ => filter d p (fuel - 1)
        else filter d p (fuel - 1)
  decreasing_by
    apply Nat.sub_lt
    · exact Nat.zero_lt_of_ne_zero (by intro h; simp_all only [beq_iff_eq]; contradiction)
    · exact Nat.zero_lt_one

@[inline] partial def Unbounded.filter
  [Inhabited r]
  (p : a → Bool) : Pipe a a m r :=
    Request PUnit.unit fun a =>
      if p a then Respond a fun _ => filter p
      else filter p

@[inline] def Fueled.filterM
  [Monad m]
  (d : r)
  (p : a → m Bool)
  : Nat → Pipe a a m r
  | 0 => Pure d
  | fuel+1 =>
      Request PUnit.unit fun a => do
        let pass ← p a
        if pass then
          Respond a fun _ => filterM d p fuel
        else
          filterM d p fuel

@[inline] partial def Unbounded.filterM
  [Inhabited r]
  (p : a → m Bool) : Pipe a a m r :=
    Request PUnit.unit fun a => do
      let pass ← p a
      if pass then
        Respond a fun _ => filterM p
      else
        filterM p

@[inline] def take : Nat -> Pipe a a m PUnit
  | 0 => .Pure ()
  | n+1 => .Request () (fun a => .Respond a (fun _ => take n))

@[inline] def Fueled.takeWhile (p : a → Bool) (d : r) (fuel : Nat) : Pipe a a m PUnit :=
  match fuel with
  | 0 => Pure ()
  | Nat.succ fuel' =>
    request () >>= fun a_val => if p a_val then respond a_val >>= fun _ => takeWhile p d fuel' else Pure ()

@[inline] partial def Unbounded.takeWhile (p : a → Bool) : Pipe a a m PUnit :=
  request () >>= fun a_val => if p a_val then respond a_val >>= fun _ => takeWhile p else Pure ()

@[inline] def replicateP_ (n : Nat) (act : Pipe a a m PUnit) : Pipe a a m PUnit :=
  match n with
  | 0 => Pure ()
  | n'+1 => act >>= fun _ => replicateP_ n' act

@[inline] def Fueled.drop (fuel_for_cat : Nat) (d : r) : Nat -> Pipe a a m r
  | 0 => Fueled.cat d fuel_for_cat
  | n_to_drop+1 => .Request () (fun _ => Fueled.drop fuel_for_cat d n_to_drop)

@[inline] def Unbounded.drop : Nat -> Pipe a a m PUnit
  | 0 => Unbounded.cat
  | n+1 => .Request () (fun _ => Unbounded.drop n)

-- partial def Proxy.dropWhile (p : a -> Bool) : Pipe a a m PUnit :=

@[inline] def Fueled.concat (d : r) (fuel : Nat) : Pipe (List a) a m r :=
  forP (Proxy.Fueled.cat d fuel) (·.forM Proxy.respond)

@[inline] private def Fueled.findIndices.go
  {a r : Type 0}
  (p : a → Bool) (d : r) (fuel i : Nat) : Pipe a Nat m r :=
  if fuel == 0 then
    Pure d
  else
    Request PUnit.unit fun a =>
      if p a then
        Respond i fun _ => go p d (fuel - 1) (i + 1)
      else
        go p d (fuel - 1) (i + 1)
  termination_by fuel
  decreasing_by
    apply Nat.sub_lt
    · exact Nat.zero_lt_of_ne_zero (by intro h; simp_all [beq_iff_eq];)
    · exact Nat.zero_lt_one

@[inline] def Fueled.findIndices (p : a → Bool) (d : r) (fuel : Nat) : Pipe a Nat m r := Proxy.Fueled.findIndices.go p d fuel 0

@[inline] private partial def Unbounded.findIndices.go
  {a : Type 0} [Inhabited r]
  (p : a → Bool) : Nat → Pipe a Nat m r
  | i =>
      Request PUnit.unit fun a =>
        if p a then
          Respond i fun _ => go p (i + 1)
        else
          go p (i + 1)

@[inline] def Unbounded.findIndices [Inhabited r] (p : a → Bool) : Pipe a Nat m r := Proxy.Unbounded.findIndices.go p 0

@[inline] def Fueled.elemIndices [BEq a] (x_val : a) (d : r) (fuel : Nat) : Pipe a Nat m r := Proxy.Fueled.findIndices (· == x_val) d fuel
@[inline] def Unbounded.elemIndices [Inhabited r] [BEq a] (x_val : a) : Pipe a Nat m r := Proxy.Unbounded.findIndices (· == x_val)

@[inline] def Fueled.scan
  (step : s → a → s)
  (done : s → b)
  (d : r)
  (acc : s)
  (fuel : Nat)
  : Pipe a b m r :=
  if fuel == 0 then
    Proxy.Pure d
  else
    Proxy.Request PUnit.unit fun a =>
      let acc' := step acc a
      Proxy.Respond (done acc') fun _ =>
        Proxy.Fueled.scan step done d acc' (fuel - 1)
  decreasing_by
    apply Nat.sub_lt
    · exact Nat.zero_lt_of_ne_zero (by intro h; simp_all only [beq_iff_eq]; contradiction)
    · exact Nat.zero_lt_one

@[inline] partial def Unbounded.scan [Inhabited r] (step : s → a → s) (done : s → b) (acc : s) : Pipe a b m r :=
  .Request () fun a =>
    let acc' := step acc a
    .Respond (done acc') fun _ => Unbounded.scan step done acc'

@[inline] def Fueled.scanM
  [Monad m]
  (step : s → a → m s)
  (done : s → m b)
  (d : r)
  (acc : s)
  (fuel : Nat)
  : Pipe a b m r :=
  if fuel == 0 then
    Proxy.Pure d
  else
    Proxy.Request PUnit.unit fun a =>
      Proxy.M (step acc a) fun acc' =>
        Proxy.M (done acc') fun b =>
          Proxy.Respond b fun _ =>
            scanM step done d acc' (fuel - 1)
  decreasing_by
    apply Nat.sub_lt
    · exact Nat.zero_lt_of_ne_zero (by intro h; simp_all only [beq_iff_eq]; contradiction)
    · exact Nat.zero_lt_one

@[inline] partial def Unbounded.scanM [Inhabited r] [Monad m] (step : s → a → m s) (done : s → m b) (acc : s) : Pipe a b m r :=
  Proxy.Request PUnit.unit fun a =>
    Proxy.M (step acc a) fun acc' =>
      Proxy.M (done acc') fun b =>
        Proxy.Respond b fun _ => Unbounded.scanM step done acc'

@[inline] def Fueled.chain
  [Monad m]
  (f : a → m PUnit) (fuel : Nat) (d : r) : Pipe a a m r :=
  if fuel == 0 then
    Proxy.Pure d
  else
    Proxy.Request PUnit.unit fun a =>
      Proxy.M (f a) fun _ =>
        Proxy.Respond a fun _ =>
          Proxy.Fueled.chain f (fuel - 1) d
  decreasing_by
    apply Nat.sub_lt
    · exact Nat.zero_lt_of_ne_zero (by intro h; simp_all only [beq_iff_eq]; contradiction)
    · exact Nat.zero_lt_one

@[inline] partial def Unbounded.chain
  [Inhabited r] [Monad m]
  (f : a → m PUnit) : Pipe a a m r :=
  Proxy.Request PUnit.unit fun a =>
    Proxy.M (f a) fun _ =>
      Proxy.Respond a fun _ =>
        Proxy.Unbounded.chain f

@[inline] def fold
  {b acc result : Type u}
  [Monad m]
  (step : acc → b → acc)
  (done : acc → result)
  (begin_val : acc)
  (p : Producer b m PUnit) : m result :=
  match p with
  | Request v _ => PEmpty.elim v
  | Pure _ => pure (done begin_val)
  | M mx k => do fold step done begin_val (k (← mx))
  | Respond a fu =>
      let acc' := step begin_val a
      fold step done acc' (fu .unit)

@[inline] def fold'
  {b acc result : Type u}
  [Monad m]
  (step : acc → b → acc)
  (done : acc → result)
  (begin_val : acc) :
  Producer b m r → m (result × r)
  | Request v _ => PEmpty.elim v
  | Pure r => pure (done begin_val, r)
  | M mx k => do fold' step done begin_val (k (← mx))
  | Respond a fu =>
      let acc' := step begin_val a
      fold' step done acc' (fu .unit)

@[inline] def foldM
  {b acc res : Type u}
  {m : Type u → Type u}
  [Monad m]
  (step : acc → b → m acc)
  (begin_m_x : m acc)
  (done : acc → m res)
  (p0 : Producer b m PUnit) : m res :=
  let rec go (p : Producer b m PUnit) (mx : m acc) : m res :=
    match p with
    | Request v _ => PEmpty.elim v
    | Pure _ => do done (← mx)
    | M act cont => do go (cont (← act)) mx
    | Respond a fu => do go (fu .unit) (step (← mx) a)
  go p0 begin_m_x

@[inline] def foldM'
  {b acc res r : Type u}
  {m : Type u → Type u}
  [Monad m]
  (step : acc → b → m acc)
  (begin_m_x : m acc)
  (done : acc → m res)
  (p0 : Producer b m r) : m (res × r) :=
  let rec go (p : Producer b m r) (mx : m acc) : m (res × r) :=
    match p with
    | Request v _ => PEmpty.elim v
    | Pure r => do pure ((← done (← mx)), r)
    | M act cont => do go (cont (← act)) mx
    | Respond a fu => do go (fu .unit) (step (← mx) a)
  go p0 begin_m_x

@[inline] def null
  {b : Type 0} -- BC of Bool
  [Monad m]
  (p : Producer b m PUnit) : m Bool :=
  match p with
  | Request v _ => PEmpty.elim v
  | Pure _ => pure true
  | M act cont => do null (cont (← act))
  | Respond _ _ => pure false

@[inline] def all
  {b : Type 0}
  [Monad m]
  (p : b → Bool) (p0 : Producer b m PUnit) : m Bool :=
  match p0 with
  | Request v _ => PEmpty.elim v
  | Pure _ => pure true
  | M act cont => do all p (cont (← act))
  | Respond x fu =>
      if p x then all p (fu .unit)
      else pure false

@[inline] def any
  {b : Type 0}
  [Monad m]
  (p : b → Bool) (p0 : Producer b m PUnit) : m Bool :=
  match p0 with
  | Request v _ => PEmpty.elim v
  | Pure _ => pure false
  | M act cont => do any p (cont (← act))
  | Respond x fu =>
      if p x then pure true
      else any p (fu .unit)

@[inline] def and [Monad m] : Producer Bool m PUnit -> m Bool := all id
@[inline] def or [Monad m] : Producer Bool m PUnit -> m Bool := any id
@[inline] def elem [Monad m] [BEq b] (b_val : b) : Producer b m PUnit -> m Bool := any (· == b_val)
@[inline] def notElem [Monad m] [BEq b] (b_val : b) : Producer b m PUnit -> m Bool := any (Bool.not ∘ (· == b_val))

@[inline] def head
  {b : Type u}
  {m : Type u → Type u}
  [Monad m]
  (p : Producer b m PUnit) : m (Option b) :=
match p with
| Request v _ => PEmpty.elim v
| Pure _ => pure none
| M mx k => do head (k (← mx))
| Respond a _fu => pure (some a)

@[inline] def Fueled.find
  {a : Type u} {m : Type u → Type u}
  [Monad m]
  (p : a → Bool) (fuel : Nat) (prod : Producer a m PUnit) : m (Option a) :=
  Proxy.head (prod >-> Proxy.Fueled.filter PUnit.unit p fuel)

@[inline] def Unbounded.find
  {a : Type u} {m : Type u → Type u}
  [Monad m] [Inhabited r]
  (p : a → Bool) (prod : Producer a m PUnit) : m (Option a) :=
  Proxy.head (prod >-> Proxy.Unbounded.filter p)

@[inline] def Fueled.findIndex
  {a : Type 0}
  [Monad m]
  (p : a → Bool) (fuel : Nat) (prod : Producer a m PUnit) : m (Option Nat) :=
  Proxy.head (prod >-> Proxy.Fueled.findIndices p .unit fuel)

@[inline] def Unbounded.findIndex
  {a : Type 0}
  [Monad m] [Inhabited r]
  (p : a → Bool) (prod : Producer a m PUnit) : m (Option Nat) :=
  Proxy.head (prod >-> Proxy.Unbounded.findIndices p)

@[inline] def Fueled.index
  {a : Type 0}
  [Monad m]
  (n : Nat) (fuel : Nat) (prod : Producer a m PUnit) : m (Option a) :=
  Proxy.head (prod >-> Proxy.Fueled.drop fuel PUnit.unit n)

@[inline] def Unbounded.index
  {a : Type 0}
  [Monad m]
  (n : Nat) (prod : Producer a m PUnit) : m (Option a) :=
  Proxy.head (prod >-> Proxy.Unbounded.drop n)

@[inline] private def last.go [Monad m] (d : b) : Producer b m PUnit -> m b
  | .Request v _ => PEmpty.elim v
  | .Respond b cont => go b (cont ())
  | .M op cont => do go d (cont (← op))
  | .Pure _ => pure d

@[inline] def last [Monad m] : Producer b m PUnit -> m (Option b)
  | .Request v _ => PEmpty.elim v
  | .Respond b cont => do return .some (<- last.go b (cont ()))
  | .M op cont => do last (cont (← op))
  | .Pure _ => pure none

@[inline] def length [Monad m] : Producer b m PUnit -> m Nat := fold (fun (n_val : Nat) (_ : b) => n_val + 1) id 0

@[inline] def maximum [Monad m] : Producer Nat m PUnit -> m (Option Nat) :=
  let step (x_opt : Option Nat) (z : Nat) :=
    match x_opt with
    | .none => .some z
    | .some a' => .some (max a' z)
  fold step id .none

@[inline] def minimum [Monad m] : Producer Nat m PUnit -> m (Option Nat) :=
  let step (x_opt : Option Nat) (z : Nat) :=
    match x_opt with
    | .none => .some z
    | .some a' => .some (min a' z)
  fold step id .none

@[inline] def sum [Monad m] : Producer Nat m PUnit -> m Nat := fold Nat.add id 0
@[inline] def product [Monad m] : Producer Nat m PUnit -> m Nat := fold Nat.mul id 1

@[inline] def toList : Proxy PEmpty PUnit PUnit b Id PUnit -> List b
  | Request v _ => PEmpty.elim v
  | Pure _ => []
  | Respond a_val fu => a_val :: toList (fu .unit)
  | M mx k => toList (k (Id.run mx))

@[inline] def toListM [Monad m] : Producer b m PUnit → m (List b)
  | .Pure _ => pure []
  | .Request v _ => PEmpty.elim v
  | .Respond a_val fu => do
    let rest ← toListM (fu ())
    pure (a_val :: rest)
  | .M mx k => do
    let x ← mx
    toListM (k x)

-------------------- MY maps

@[inline] def mapUpstreamInput
  (f : a' → A') : Proxy a' a b' b m r → Proxy A' a b' b m r
  | Request a' cont => Request (f a') (fun x => mapUpstreamInput f (cont x))
  | Respond b  cont => Respond b (fun x => mapUpstreamInput f (cont x))
  | M op cont       => M op (fun x => mapUpstreamInput f (cont x))
  | Pure r          => Pure r
  termination_by structural p => p

@[inline] def mapDownstreamInput
  (f : A → a) : Proxy a' a b' b m r → Proxy a' A b' b m r
  | Request a' cont => Request a' (fun x => mapDownstreamInput f (cont (f x)))
  | Respond b  cont => Respond b (fun x => mapDownstreamInput f (cont x))
  | M op cont       => M op (fun x => mapDownstreamInput f (cont x))
  | Pure r          => Pure r
  termination_by structural p => p

@[inline] def mapUpstreamOutput
  (f : B' → b') : Proxy a' a b' b m r → Proxy a' a B' b m r
  | Request a' cont => Request a' (fun x => mapUpstreamOutput f (cont x))
  | Respond b cont  => Respond b (fun b' => mapUpstreamOutput f (cont (f b')))
  | M op cont       => M op (fun x => mapUpstreamOutput f (cont x))
  | Pure r          => Pure r
  termination_by structural p => p

@[inline] def mapDownstreamOutput
  (f : b → B) : Proxy a' a b' b m r → Proxy a' a b' B m r
  | Request a' cont => Request a' (fun x => mapDownstreamOutput f (cont x))
  | Respond b cont  => Respond (f b) (fun x => mapDownstreamOutput f (cont x))
  | M op cont       => M op (fun x => mapDownstreamOutput f (cont x))
  | Pure r          => Pure r
  termination_by structural p => p

--------------------

private def mapUpstreamInputWithIndex.go
  (f : Nat → a' → A') (p : Proxy a' a b' b m r) (acc : Nat) : Proxy A' a b' b m r :=
  match p with
  | Request a' cont => Request (f acc a') (fun x => go f (cont x) (acc + 1))
  | Respond b cont => Respond b (fun x => go f (cont x) acc)
  | M op cont => M op (fun x => go f (cont x) acc)
  | Pure r => Pure r
  termination_by structural p

@[inline] def mapUpstreamInputWithIndex (f : Nat → a' → A') (p : Proxy a' a b' b m r) : Proxy A' a b' b m r := mapUpstreamInputWithIndex.go f p 0

@[inline] def enumerateUpstreamInput : Proxy a' a b' b m r -> Proxy (Nat × a') a b' b m r := mapUpstreamInputWithIndex (fun i a' => (i, a'))

---------
private def mapDownstreamInputWithIndex.go
  (f : Nat → A → a) (p : Proxy a' a b' b m r) (acc : Nat) : Proxy a' A b' b m r :=
  match p with
  | Request a' cont => Request a' (fun x => go f (cont (f acc x)) (acc + 1))
  | Respond b cont  => Respond b (fun x => go f (cont x) acc)
  | M op cont       => M op (fun x => go f (cont x) acc)
  | Pure r          => Pure r
  termination_by structural p

@[inline] def mapDownstreamInputWithIndex (f : Nat → A → a) (p : Proxy a' a b' b m r) : Proxy a' A b' b m r :=
  mapDownstreamInputWithIndex.go f p 0

---------

@[inline] private def mapUpstreamOutputWithIndex.go
  (f : Nat → B' → b') (p : Proxy a' a b' b m r) (acc : Nat) : Proxy a' a B' b m r :=
  match p with
  | Request a' cont => Request a' (fun x => go f (cont x) acc)
  | Respond b cont  => Respond b (fun b' => go f (cont (f acc b')) (acc + 1))
  | M op cont       => M op (fun x => go f (cont x) acc)
  | Pure r          => Pure r
  termination_by structural p

@[inline] def mapUpstreamOutputWithIndex (f : Nat → B' → b') (p : Proxy a' a b' b m r) : Proxy a' a B' b m r :=
  mapUpstreamOutputWithIndex.go f p 0
---------

private def mapDownstreamOutputWithIndex.go
  (f : Nat → b → B) (p : Proxy a' a b' b m r) (acc : Nat) : Proxy a' a b' B m r :=
  match p with
  | Request a' cont => Request a' (fun x => go f (cont x) acc)
  | Respond b cont  => Respond (f acc b) (fun x => go f (cont x) (acc + 1))
  | M op cont       => M op (fun x => go f (cont x) acc)
  | Pure r          => Pure r
  termination_by structural p

@[inline] def mapDownstreamOutputWithIndex (f : Nat → b → B) (p : Proxy a' a b' b m r) : Proxy a' a b' B m r :=
  mapDownstreamOutputWithIndex.go f p 0

@[inline] def enumerateDownstreamOutput : Proxy a' a b' b m r → Proxy a' a b' (Nat × b) m r :=
  mapDownstreamOutputWithIndex (fun i b => (i, b))

-------------------- MY PRELUDE

@[inline] def fromList : List b → Producer b m PUnit
| []      => .Pure ()
| (x::xs) => .Respond x (fun _ => fromList xs)

@[inline] def fromArray : Array b -> Producer b m PUnit :=
  fromList ∘ Array.toList

-- Replicate an element n times
@[inline] def replicate (n : Nat) (x : b) : Producer b m PUnit := fromList (List.replicate n x)

@[inline] private partial def Unbounded.enumerate.go [Inhabited r] (i : Nat) : Proxy PUnit a b' (Nat × a) m r :=
  .Request () (fun a => .Respond (i, a) (fun _ => go (i + 1)))

@[inline] def Unbounded.enumerate [Inhabited r] : Proxy PUnit a b' (Nat × a) m r /- Pipe a (Nat × a) m r -/ := enumerate.go 0

@[inline] partial def Unbounded.print [ToString a] [MonadLift IO m] [Inhabited r] : Pipe a a m r :=
  .Request () (fun a =>
    .M (MonadLift.monadLift (IO.println (toString a))) (fun _ =>
      .Respond a (fun _ => print)))

-- Prepend an element to a producer
@[inline] def cons (x : b) (p : Producer b m r) : Producer b m r := Respond x (fun _ => p)

-- Append an element to a producer
@[inline] def snoc (x : b) (p : Producer b m r) : Producer b m r := p.bind fun r => Respond x (fun _ => Pure r)

-- Buffer n elements: collect list of next n inputs, emit when full
partial def Unbounded.buffer [Inhabited r] (n : Nat) : Pipe a (List a) m r :=
  match n with
  | 0   => Pure default
  | n+1 => do
    let x <- request .unit
    let xs <- buffer n
    Respond (x::xs) fun _ => Unbounded.drain

-- https://hackage.haskell.org/package/pipes-4.3.16/docs/Pipes-Prelude.html#v:tee
-- Transform a Consumer to a Pipe that reforwards all values further downstream
-- def Unbounded.tee : Consumer a m r -> Pipe a a m r :=

-- Infinite cycle through list
partial def Unbounded.cycle [Inhabited r] [Inhabited a] (xs : List a) : Producer a m r :=
  match xs with
  | []     => Pure default
  | y::ys  => Respond y (fun _ => cycle (ys ++ [y]))

-- Interleave two producers round-robin
-- partial def Unbounded.interleave (p1 p2 : Producer b m PUnit) : Producer b m PUnit :=
--   match p1 with
--   | Respond x k => Respond x (fun _ => interleave p2 (k ()))
--   | M mx k      => M (mx.map fun ⟨p1'⟩ => p1') fun p1' => interleave p1' p2
--   | _           => p2

-- Remove consecutive duplicates from a stream
partial def Unbounded.group [Inhabited r] [BEq a] : Pipe a (List a) m r :=
  await >>= fun x =>
  let rec loop [Inhabited r] (prev : a) : Pipe a (List a) m r :=
    await >>= fun y =>
    if y == prev then loop prev else Respond [prev] fun _ => loop y
  loop x

-- Drop duplicates (unique consecutive only)
partial def Unbounded.distinct [BEq a] [Inhabited r] : Pipe a a m r :=
  await >>= fun x =>
  let rec loop [Inhabited r] (prev : a) : Pipe a a m r :=
    await >>= fun y =>
    if y == prev then loop prev else Respond y fun _ => loop y
  Respond x fun _ => loop x

-- Repeat a producer infinitely
partial def Unbounded.repeatP
  (p : Producer b m PUnit) : Producer b m PUnit :=
  let rec go : Producer b m PUnit :=
    p *> go
  go

@[inline] def failure [Alternative m] : Proxy a' a b' b m r := Proxy.monadLift Alternative.failure

-- https://github.com/Gabriella439/pipes/commit/08e7302f43dbf2a40bd367c5ee73ee3367e17768
-- private def orElse.convertToM [Monad m] : Proxy PEmpty a b' PEmpty m r → m r
--   | .Request v _ => PEmpty.elim v
--   | .Respond v _ => PEmpty.elim v
--   | .M mx k => mx >>= (fun x => convertToM (k x))
--   | .Pure xr => pure xr
-- partial def orElse {a b' r : Type 0} {m : Type 0 -> Type 0} [Monad m] [Alternative m] [Inhabited r]
--   (x : Proxy PEmpty a b' PEmpty m r) (y : PUnit → Proxy PEmpty a b' PEmpty m r) : Proxy PEmpty a b' PEmpty m r :=
--   match x with
--     | .Request v k => PEmpty.elim v -- .Request xa' (fun a => orElse (k a) y)
--     | .Respond v k => PEmpty.elim v -- .Respond xb (fun b' => orElse (k b') y)
--     | .M mx k => .M (Alternative.orElse mx (fun _ => orElse.convertToM (y PUnit.unit))) (fun x => orElse (k x) y)
--     | .Pure xr => .Pure xr
-- @[inline] instance [Monad m] [Alternative m] : Alternative (Proxy a' a b' b m) := ⟨failure, Proxy.orElse⟩
-- instance [Monad m] [Alternative m] [LawfulAlternative m] : LawfulAlternative (Proxy a' a b' b m) where
--   map_failure g := by sorry
--   failure_seq x := by sorry
--   map_orElse x y g := by rfl
--   orElse_failure x := by sorry
--   failure_orElse y := by sorry
--   orElse_assoc x y z := by sorry
-- namespace AlternativeTest
--   def testAlt1 : Proxy PEmpty PUnit PUnit PEmpty Option String := failure
--   def testAlt2 : Proxy PEmpty PUnit PUnit PEmpty Option String := Pure "world"
--   #check runEffect testAlt1 = .none
--   #check runEffect testAlt2 = .some "world"
-- end AlternativeTest

end Proxy
--------------------------------------------------------------------------------
-- Theorems from PipesLawsPrelude
--------------------------------------------------------------------------------

namespace PipesLawsPrelude

open Proxy

lemma for_yield_general (s : Proxy x' x PUnit b m r) :
  s //> (respond : b → Proxy x' x PUnit b m PUnit) = s := by
  induction s with
  | Request xa' k ih =>
    simp only [forP, respond]
    congr
    funext a_val
    exact ih a_val
  | Respond xb k ih =>
    simp only [Proxy.forP, Proxy.respond, Bind.bind]
    simp_all only [Proxy.bind]
  | M mx k ih =>
    simp only [forP, respond]
    congr
    funext x_val
    exact ih x_val
  | Pure xr =>
    simp only [forP, respond]

theorem map_id {a : Type} (d : r) (fuel : Nat) :
  Fueled.mapPipe (a := a) (b := a) (m := m) d fuel (fun x => x) = Fueled.cat d fuel := by
  -- apply for_yield_general
  sorry

theorem map_compose [Inhabited r] -- TODO: prove termination of pullR and pushR
  {m : Type → Type} (d : r) (fuel : Nat)
  (f : a → b) (g : b → c) :
  Fueled.mapPipe d fuel (g ∘ f)
    = Fueled.mapPipe d fuel f
      >-> Fueled.mapPipe (m := m) d fuel g := by
        unfold Fueled.mapPipe
        simp only [Function.comp]
        -- simp_all only [Proxy.respond]
        sorry

theorem toListM_each_id {a : Type 0} {m : Type 0 -> Type 0} [Monad m] (xs : List a) :
  toListM (each xs) = Pure.pure (f := m) xs := by
  induction xs with
  | nil =>
    simp only [each, Proxy.fromList, toListM]
    simp_all only [List.forM_eq_forM, List.forM_nil]
    rfl
  | cons x' xs' ih =>
    simp only [each, Proxy.fromList, toListM, List.cons.injEq]
    simp_all only [List.forM_eq_forM, List.forM_cons, respond]
    sorry

end PipesLawsPrelude
