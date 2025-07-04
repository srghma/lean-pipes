-- This module serves as the root of the `Pipes` library.
-- Import modules here that should be built as part of the library.
import Pipes.Core
import Pipes.Internal
import Pipes.CoreLaws

-- import Canonical
-- import Aesop
import Init.Control.State
--### import Batteries.Control.AlternativeMonad
--### import Mathlib.CategoryTheory.Category.Basic
--### import Mathlib.CategoryTheory.Functor.Basic

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

def Fueled.cat (default : r) (fuel : Nat) : Pipe a a m r := Fueled.pull default fuel ()

def Unbounded.cat [Inhabited r] : Pipe a a m r := Unbounded.pull ()

def connect
  (p1 : Proxy a' a PUnit b m r)
  (p2 : Proxy PUnit b c' c m r) :
  Proxy a' a c' c m r :=
  (fun (_ : PUnit) => p1) +>> p2

infixl:60 " >-> " => connect
infixl:60 " <-< " => fun x y => connect y x

-- This next is DISALLOWED
--
-- def next
--   [_root_.Pure m] [Bind m]
--   (p : Producer b m r) :
--   m (r ⊕ (a × (Producer b m r))) :=
--   match p with
--   | Request v _  => PEmpty.elim v
--   | Respond a fu => pure (Sum.inr (a, fun _ => fu ()))
--   | M mx k => mx >>= fun x => Proxy.next (k x)
--   | Pure r => pure (Sum.inl r)
--
-- So instead
inductive ProxyNextStep.{u} (b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
  | Respond {x : Type u} (downstreamOutput : Option b) (op : m x) (cont : x → ProxyNextStep b m r) : ProxyNextStep b m r
  | Pure    : r → ProxyNextStep b m r

def next [_root_.Pure m] (p : Producer b m r) : ProxyNextStep b m r :=
  match p with
  | Request v _ => PEmpty.elim v
  | Respond b fu => ProxyNextStep.Respond (.some b) (pure ()) (fun _ => Proxy.next (fu ()))
  | M op cont => ProxyNextStep.Respond .none op (fun x => Proxy.next (cont x))
  | Pure r => ProxyNextStep.Pure r
  termination_by structural p

-- each = every, in coq too
def each (xs : List b) : Producer b m PUnit :=
  xs.forM respond

def every (xs : List b) : Producer b m PUnit :=
  xs.foldlM (fun _ => respond) ()

--------------------------

-- Definition repeatM `{Monad m} `(x : m a) : Producer' a m r :=
--   fun _ _ => lift x >~ cat (n:=n) (d:=d).
--
-- replicateM :: Monad m => Int -> m a -> Producer' a m ()
-- replicateM n m = lift m >~ take n

def Fueled.drain (d : r) (fuel : Nat) : Consumer_ a m r :=
  -- forP (Proxy.Fueled.cat d fuel) (fun _ => Proxy.Pure ())
  match fuel with
  | 0     => .Pure d
  | fuel' + 1 => .Request .unit (fun _ => Fueled.drain d fuel')

partial def Unbounded.drain [Inhabited r] : Consumer_ a m r :=
  -- forP (Proxy.Unbounded.cat) (fun _ => Proxy.Pure ())
  .Request .unit (fun _ => drain)

-- In coq - just `map`, bad name
def Fueled.mapPipe (d : r) (fuel : Nat) (f : a → b) : Pipe a b m r :=
  -- forP (Proxy.Fueled.cat d fuel) (fun val => Proxy.respond (f val))
  match fuel with
  | 0     => .Pure d
  | fuel' + 1 => .Request .unit (fun a => .Respond (f a) (fun _ => Fueled.mapPipe d fuel' f))

partial def Unbounded.mapPipe [Inhabited r] (f : a → b) : Pipe a b m r :=
  forP (Proxy.Unbounded.cat) (fun val => Proxy.respond (f val))
  -- .Request () (fun a => .Respond (f a) (fun _ => mapPipe f))

-- In coq - just `mapM`, bad name
def Pipe.Fueled.mapM [Monad m] (f : a → m b) (d : r) (fuel : Nat) : Pipe a b m r :=
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

partial def Pipe.Unbounded.mapM [Inhabited r] (f : a -> m b) : Pipe a b m r :=
  .Request () (fun a => .M (f a) (fun b => .Respond b (fun _ => mapM f)))

def Fueled.mapM_ [Monad m] (f : a → m PUnit) (d : r) (fuel : Nat) : Consumer a m r :=
  forP (Proxy.Fueled.cat d fuel) (fun val => monadLift (f val))

partial def Unbounded.mapM_ [Inhabited r] (f : a → m PUnit) : Consumer a m r :=
  forP Proxy.Unbounded.cat (fun val => monadLift (f val))
  -- .Request ?? (fun a => .M (f a) (fun _ => Unbounded.mapM_ f))

def Pipe.Fueled.sequence [Monad m] (d : r) (fuel : Nat) : Pipe (m a) a m r :=
  mapM id d fuel

partial def Pipe.Unbounded.sequence [Inhabited r] : Pipe (m a) a m r :=
  mapM id

def Fueled.mapFoldable (d : r) (fuel : Nat) (f : a → List b) : Pipe a b m r :=
  forP (Proxy.Fueled.cat d fuel) (fun x => (f x).forM Proxy.respond)

def whenP (cond : Bool) (action : Pipe a a m PUnit) : Pipe a a m PUnit :=
  if cond then action else Pure ()

-- NOTE: coq uses `forP` version
def Fueled.ForPVersion.filter (d : r) (fuel : Nat) (p : a → Bool) : Pipe a a m r :=
  forP (Proxy.Fueled.cat d fuel) (fun x => whenP (p x) (Proxy.yield x))

def Fueled.filter
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

partial def Unbounded.filter
  [Inhabited r]
  (p : a → Bool) : Pipe a a m r :=
    Request PUnit.unit fun a =>
      if p a then Respond a fun _ => filter p
      else filter p

def Fueled.filterM
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

partial def Unbounded.filterM
  [Inhabited r]
  (p : a → m Bool) : Pipe a a m r :=
    Request PUnit.unit fun a => do
      let pass ← p a
      if pass then
        Respond a fun _ => filterM p
      else
        filterM p

def take : Nat -> Pipe a a m PUnit
  | 0 => .Pure ()
  | n+1 => .Request () (fun a => .Respond a (fun _ => take n))

def Fueled.takeWhile (p : a → Bool) (d : r) (fuel : Nat) : Pipe a a m PUnit :=
  match fuel with
  | 0 => Pure ()
  | Nat.succ fuel' =>
    request () >>= fun a_val => if p a_val then respond a_val >>= fun _ => takeWhile p d fuel' else Pure ()

partial def Unbounded.takeWhile (p : a → Bool) : Pipe a a m PUnit :=
  request () >>= fun a_val => if p a_val then respond a_val >>= fun _ => takeWhile p else Pure ()

def replicateP_ (n : Nat) (act : Pipe a a m PUnit) : Pipe a a m PUnit :=
  match n with
  | 0 => Pure ()
  | n'+1 => act >>= fun _ => replicateP_ n' act

def Fueled.drop (fuel_for_cat : Nat) (d : r) : Nat -> Pipe a a m r
  | 0 => Fueled.cat d fuel_for_cat
  | n_to_drop+1 => .Request () (fun _ => Fueled.drop fuel_for_cat d n_to_drop)

def Unbounded.drop : Nat -> Pipe a a m PUnit
  | 0 => Unbounded.cat
  | n+1 => .Request () (fun _ => Unbounded.drop n)

-- partial def Proxy.dropWhile (p : a -> Bool) : Pipe a a m PUnit :=

def Fueled.concat (d : r) (fuel : Nat) : Pipe (List a) a m r :=
  forP (Proxy.Fueled.cat d fuel) (·.forM Proxy.respond)

private def Fueled.findIndices.go
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

def Fueled.findIndices (p : a → Bool) (d : r) (fuel : Nat) : Pipe a Nat m r := Proxy.Fueled.findIndices.go p d fuel 0

private partial def Unbounded.findIndices.go
  {a : Type 0} [Inhabited r]
  (p : a → Bool) : Nat → Pipe a Nat m r
  | i =>
      Request PUnit.unit fun a =>
        if p a then
          Respond i fun _ => go p (i + 1)
        else
          go p (i + 1)

def Unbounded.findIndices [Inhabited r] (p : a → Bool) : Pipe a Nat m r := Proxy.Unbounded.findIndices.go p 0

def Fueled.elemIndices [BEq a] (x_val : a) (d : r) (fuel : Nat) : Pipe a Nat m r := Proxy.Fueled.findIndices (· == x_val) d fuel
def Unbounded.elemIndices [Inhabited r] [BEq a] (x_val : a) : Pipe a Nat m r := Proxy.Unbounded.findIndices (· == x_val)

def Fueled.scan
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

partial def Unbounded.scan [Inhabited r] (step : s → a → s) (done : s → b) (acc : s) : Pipe a b m r :=
  .Request () fun a =>
    let acc' := step acc a
    .Respond (done acc') fun _ => Unbounded.scan step done acc'

def Fueled.scanM
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

partial def Unbounded.scanM [Inhabited r] [Monad m] (step : s → a → m s) (done : s → m b) (acc : s) : Pipe a b m r :=
  Proxy.Request PUnit.unit fun a =>
    Proxy.M (step acc a) fun acc' =>
      Proxy.M (done acc') fun b =>
        Proxy.Respond b fun _ => Unbounded.scanM step done acc'

def Fueled.scanWithStateM
  [Monad m]
  (step : x → a → m x)
  (begin_x : m x)
  (d : r)
  : Nat → Pipe a a m r :=
  fun fuel =>
    if fuel == 0 then
      Pure d
    else
      let rec go (current_x : x) (remaining_fuel : Nat) : Pipe a a m r :=
        if remaining_fuel == 0 then
          .Pure d
        else
          .Request PUnit.unit fun (input_a : a) =>
            .M (step current_x input_a) fun (next_x : x) =>
              .Respond input_a fun _ =>
                go next_x (remaining_fuel - 1)
        termination_by remaining_fuel
        decreasing_by
        apply Nat.sub_lt
        · exact Nat.zero_lt_of_ne_zero (by intro h; simp_all only [beq_iff_eq]; contradiction)
        · exact Nat.zero_lt_one
      .M begin_x fun (initial_x : x) => go initial_x (fuel - 1)

partial def Unbounded.scanWithStateM
  [Inhabited r]
  [Monad m]
  (step : x → a → m x)
  (begin_x : m x)
  : Pipe a a m r :=
  let rec go [Inhabited r] (current_x : x) : Pipe a a m r :=
    Request PUnit.unit fun (input_a : a) =>
      M (step current_x input_a) fun (next_x : x) =>
        Respond input_a fun _ =>
          go next_x
  .M begin_x fun (initial_x : x) => go initial_x

def Fueled.chain
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

partial def Unbounded.chain
  [Inhabited r] [Monad m]
  (f : a → m PUnit) : Pipe a a m r :=
  Proxy.Request PUnit.unit fun a =>
    Proxy.M (f a) fun _ =>
      Proxy.Respond a fun _ =>
        Proxy.Unbounded.chain f

def fold
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

def fold'
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

def foldM
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

def foldM'
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

def null
  {b : Type 0} -- BC of Bool
  [Monad m]
  (p : Producer b m PUnit) : m Bool :=
  match p with
  | Request v _ => PEmpty.elim v
  | Pure _ => pure true
  | M act cont => do null (cont (← act))
  | Respond _ _ => pure false

def all
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

def any
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

def and [Monad m] : Producer Bool m PUnit -> m Bool := all id
def or [Monad m] : Producer Bool m PUnit -> m Bool := any id
def elem [Monad m] [BEq b] (b_val : b) : Producer b m PUnit -> m Bool := any (· == b_val)
def notElem [Monad m] [BEq b] (b_val : b) : Producer b m PUnit -> m Bool := any (Bool.not ∘ (· == b_val))

def head
  {b : Type u}
  {m : Type u → Type u}
  [Monad m]
  (p : Producer b m PUnit) : m (Option b) :=
match p with
| Request v _ => PEmpty.elim v
| Pure _ => pure none
| M mx k => do head (k (← mx))
| Respond a _fu => pure (some a)

def Fueled.find
  {a : Type u} {m : Type u → Type u}
  [Monad m]
  (p : a → Bool) (fuel : Nat) (prod : Producer a m PUnit) : m (Option a) :=
  Proxy.head (prod >-> Proxy.Fueled.filter PUnit.unit p fuel)

def Unbounded.find
  {a : Type u} {m : Type u → Type u}
  [Monad m] [Inhabited r]
  (p : a → Bool) (prod : Producer a m PUnit) : m (Option a) :=
  Proxy.head (prod >-> Proxy.Unbounded.filter p)

def Fueled.findIndex
  {a : Type 0}
  [Monad m]
  (p : a → Bool) (fuel : Nat) (prod : Producer a m PUnit) : m (Option Nat) :=
  Proxy.head (prod >-> Proxy.Fueled.findIndices p .unit fuel)

def Unbounded.findIndex
  {a : Type 0}
  [Monad m] [Inhabited r]
  (p : a → Bool) (prod : Producer a m PUnit) : m (Option Nat) :=
  Proxy.head (prod >-> Proxy.Unbounded.findIndices p)

def Fueled.index
  {a : Type 0}
  [Monad m]
  (n : Nat) (fuel : Nat) (prod : Producer a m PUnit) : m (Option a) :=
  Proxy.head (prod >-> Proxy.Fueled.drop fuel PUnit.unit n)

def Unbounded.index
  {a : Type 0}
  [Monad m]
  (n : Nat) (prod : Producer a m PUnit) : m (Option a) :=
  Proxy.head (prod >-> Proxy.Unbounded.drop n)

private def last.go [Monad m] (d : b) : Producer b m PUnit -> m b
  | .Request v _ => PEmpty.elim v
  | .Respond b cont => go b (cont ())
  | .M op cont => do go d (cont (← op))
  | .Pure _ => pure d

def last [Monad m] : Producer b m PUnit -> m (Option b)
  | .Request v _ => PEmpty.elim v
  | .Respond b cont => do return .some (<- last.go b (cont ()))
  | .M op cont => do last (cont (← op))
  | .Pure _ => pure none

def length [Monad m] : Producer b m PUnit -> m Nat := fold (fun (n_val : Nat) (_ : b) => n_val + 1) id 0

def maximum [Monad m] : Producer Nat m PUnit -> m (Option Nat) :=
  let step (x_opt : Option Nat) (z : Nat) :=
    match x_opt with
    | .none => .some z
    | .some a' => .some (max a' z)
  fold step id .none

def minimum [Monad m] : Producer Nat m PUnit -> m (Option Nat) :=
  let step (x_opt : Option Nat) (z : Nat) :=
    match x_opt with
    | .none => .some z
    | .some a' => .some (min a' z)
  fold step id .none

def sum [Monad m] : Producer Nat m PUnit -> m Nat := fold Nat.add id 0
def product [Monad m] : Producer Nat m PUnit -> m Nat := fold Nat.mul id 1

def toList : Proxy PEmpty PUnit PUnit b Id PUnit -> List b
  | Request v _ => PEmpty.elim v
  | Pure _ => []
  | Respond a_val fu => a_val :: toList (fu .unit)
  | M mx k => toList (k (Id.run mx))

def toListM [Monad m] : Producer b m PUnit → m (List b)
  | .Pure _ => pure []
  | .Request v _ => PEmpty.elim v
  | .Respond a_val fu => do
    let rest ← toListM (fu ())
    pure (a_val :: rest)
  | .M mx k => do
    let x ← mx
    toListM (k x)

-------------------- MY maps

def mapUpstreamInput
  (f : a' → A') : Proxy a' a b' b m r → Proxy A' a b' b m r
  | Request a' cont => Request (f a') (fun x => mapUpstreamInput f (cont x))
  | Respond b  cont => Respond b (fun x => mapUpstreamInput f (cont x))
  | M op cont       => M op (fun x => mapUpstreamInput f (cont x))
  | Pure r          => Pure r
  termination_by structural p => p

def mapDownstreamInput
  (f : A → a) : Proxy a' a b' b m r → Proxy a' A b' b m r
  | Request a' cont => Request a' (fun x => mapDownstreamInput f (cont (f x)))
  | Respond b  cont => Respond b (fun x => mapDownstreamInput f (cont x))
  | M op cont       => M op (fun x => mapDownstreamInput f (cont x))
  | Pure r          => Pure r
  termination_by structural p => p

def mapUpstreamOutput
  (f : B' → b') : Proxy a' a b' b m r → Proxy a' a B' b m r
  | Request a' cont => Request a' (fun x => mapUpstreamOutput f (cont x))
  | Respond b cont  => Respond b (fun b' => mapUpstreamOutput f (cont (f b')))
  | M op cont       => M op (fun x => mapUpstreamOutput f (cont x))
  | Pure r          => Pure r
  termination_by structural p => p

def mapDownstreamOutput
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

def mapUpstreamInputWithIndex (f : Nat → a' → A') (p : Proxy a' a b' b m r) : Proxy A' a b' b m r := mapUpstreamInputWithIndex.go f p 0

def enumerateUpstreamInput : Proxy a' a b' b m r -> Proxy (Nat × a') a b' b m r := mapUpstreamInputWithIndex (fun i a' => (i, a'))

---------
private def mapDownstreamInputWithIndex.go
  (f : Nat → A → a) (p : Proxy a' a b' b m r) (acc : Nat) : Proxy a' A b' b m r :=
  match p with
  | Request a' cont => Request a' (fun x => go f (cont (f acc x)) (acc + 1))
  | Respond b cont  => Respond b (fun x => go f (cont x) acc)
  | M op cont       => M op (fun x => go f (cont x) acc)
  | Pure r          => Pure r
  termination_by structural p

def mapDownstreamInputWithIndex (f : Nat → A → a) (p : Proxy a' a b' b m r) : Proxy a' A b' b m r :=
  mapDownstreamInputWithIndex.go f p 0

---------

private def mapUpstreamOutputWithIndex.go
  (f : Nat → B' → b') (p : Proxy a' a b' b m r) (acc : Nat) : Proxy a' a B' b m r :=
  match p with
  | Request a' cont => Request a' (fun x => go f (cont x) acc)
  | Respond b cont  => Respond b (fun b' => go f (cont (f acc b')) (acc + 1))
  | M op cont       => M op (fun x => go f (cont x) acc)
  | Pure r          => Pure r
  termination_by structural p

def mapUpstreamOutputWithIndex (f : Nat → B' → b') (p : Proxy a' a b' b m r) : Proxy a' a B' b m r :=
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

def mapDownstreamOutputWithIndex (f : Nat → b → B) (p : Proxy a' a b' b m r) : Proxy a' a b' B m r :=
  mapDownstreamOutputWithIndex.go f p 0

def enumerateDownstreamOutput : Proxy a' a b' b m r → Proxy a' a b' (Nat × b) m r :=
  mapDownstreamOutputWithIndex (fun i b => (i, b))

-------------------- MY PRELUDE

def fromList : List b → Producer b m PUnit
| []      => .Pure ()
| (x::xs) => .Respond x (fun _ => fromList xs)

def fromArray : Array b -> Producer b m PUnit :=
  fromList ∘ Array.toList

-- Replicate an element n times
def replicate (n : Nat) (x : b) : Producer b m PUnit := fromList (List.replicate n x)

private partial def Unbounded.enumerate.go [Inhabited r] (i : Nat) : Proxy PUnit a b' (Nat × a) m r :=
  .Request () (fun a => .Respond (i, a) (fun _ => go (i + 1)))

def Unbounded.enumerate [Inhabited r] : Proxy PUnit a b' (Nat × a) m r /- Pipe a (Nat × a) m r -/ := enumerate.go 0

partial def Unbounded.print [ToString a] [MonadLift IO m] [Inhabited r] : Pipe a a m r :=
  .Request () (fun a =>
    .M (MonadLift.monadLift (IO.println (toString a))) (fun _ =>
      .Respond a (fun _ => print)))

-- Prepend an element to a producer
def cons (x : b) (p : Producer b m r) : Producer b m r := Respond x (fun _ => p)

-- Append an element to a producer
def snoc (x : b) (p : Producer b m r) : Producer b m r := p.bind fun r => Respond x (fun _ => Pure r)

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

def failure [Alternative m] : Proxy a' a b' b m r := Proxy.monadLift Alternative.failure

end Proxy
