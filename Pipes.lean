-- This module serves as the root of the `Pipes` library.
-- Import modules here that should be built as part of the library.
import Pipes.Core
import Pipes.Internal

import Aesop
import Init.Control.State
import Batteries.Control.AlternativeMonad
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

@[inline, simp] abbrev Proxy.yield : b -> Proxy a' a Unit b m Unit := Proxy.respond

infixl:70 " ~> " => fun f g => f />/ g
infixl:70 " <~ " => fun f g => g />/ f

notation:70 x " >~ " y => (fun (_ : Unit) => x) >\\ y
notation:70 x " ~< " y => y >~ x

def Proxy.await : Proxy Unit a b' b m a := Proxy.request ()

@[inline] def Proxy.cat (default : r) (fuel : Nat) : Pipe a a m r := Proxy.pull default fuel ()

@[inline] def Proxy.cat_unbounded [Inhabited r] : Pipe a a m r := Proxy.pull_unbounded ()

def Proxy.connect
  (p1 : Proxy a' a Unit b m r)
  (p2 : Proxy Unit b c' c m r) :
  Proxy a' a c' c m r :=
  (fun (_ : Unit) => p1) +>> p2

infixl:60 " >-> " => Proxy.connect
infixl:60 " <-< " => fun x y => Proxy.connect y x

-- --- DISALLOWED NEXT
-- @[inline]
-- def Proxy.next
--   [_root_.Pure m] [Bind m]
--   (p : Producer a m r) :
--   m (r ⊕ (a × (Producer a m r))) :=
--   match p with
--   | Proxy.Request v _  => False.elim v
--   | Proxy.Respond a fu => pure (Sum.inr (a, fun _ => fu ()))
--   | Proxy.M mx k => mx >>= fun x => Proxy.next (k x)
--   | Proxy.Pure r => pure (Sum.inl r)
-- --- IDEA 1 : ProxyNextStep is just Proxy with disabled fields
-- inductive ProxyNextStep.{u} (b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
--   | Respond : b → (Unit → ProxyNextStep b m r) → ProxyNextStep b m r
--   | M {x : Type u} (op : m x) (cont : x → ProxyNextStep b m r) : ProxyNextStep b m r
--   | Pure    : r → ProxyNextStep b m r
-- def ProxyNextStep.fromProducer [Monad m] (p : Producer b m r) : ProxyNextStep b m r :=
--   match p with
--   | Proxy.Request v _    => Empty.elim v
--   | Proxy.Respond b fu   => (ProxyNextStep.Respond b (fun _ => ProxyNextStep.fromProducer (fu ())))
--   | Proxy.M op cont      => (ProxyNextStep.M op ((fun x => ProxyNextStep.fromProducer (cont x))))
--   | Proxy.Pure r         => (ProxyNextStep.Pure r)
---- IDEA 2 : ProxyNextStep is more complex
-- inductive ProxyNextStep.{u} (b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
--   | Respond {x : Type u} (downstreamOutput : Option b) (op : m x) (cont : x → ProxyNextStep b m r) : ProxyNextStep b m r
--   | Pure    : r → ProxyNextStep b m r
-- @[inline] def Proxy.next [Monad m] (p : Producer b m r) : ProxyNextStep b m r :=
--   match p with
--   | Proxy.Request v _ => Empty.elim v
--   | Proxy.Respond b fu => ProxyNextStep.Respond (.some b) (pure ()) (fun _ => Proxy.next (fu ()))
--   | Proxy.M op cont => ProxyNextStep.Respond .none op (fun x => Proxy.next (cont x))
--   | Proxy.Pure r => ProxyNextStep.Pure r
--   termination_by structural p
---- IDEA 3 : Can move downstreamOutput to m? yes
inductive ProxyNextStep.{u} (b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1)
  | Respond {x : Type u} (op : m (Option b × x)) (cont : x → ProxyNextStep b m r) : ProxyNextStep b m r
  | Pure    : r → ProxyNextStep b m r
@[inline] def Proxy.next [Monad m] (p : Producer b m r) : ProxyNextStep b m r :=
  match p with
  | Proxy.Request v _ => Empty.elim v
  | Proxy.Respond b fu =>
    ProxyNextStep.Respond (pure (some b, ())) (fun _ => Proxy.next (fu ()))
  | Proxy.M op cont =>
    ProxyNextStep.Respond (do
      pure (none, (← op))
    ) (fun x => Proxy.next (cont x))
  | Proxy.Pure r => ProxyNextStep.Pure r
  termination_by structural p
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
@[inline] def Proxy.each (xs : List a) : Producer a m Unit :=
  xs.forM Proxy.respond

@[inline] def Proxy.every (xs : List a) : Producer a m Unit :=
  xs.foldlM (fun _ x => Proxy.respond x) ()

theorem for_yield_f (f : b → Proxy x' x c' c m Unit) (x_val : b) :
  Proxy.yield x_val //> f = f x_val := by
  simp only [Proxy.forP, Proxy.yield, Proxy.respond]
  sorry

theorem for_yield (s : Proxy x' x Unit b m Unit) :
  s //> Proxy.yield = s := by
  simp only [Proxy.forP, Proxy.yield, Proxy.respond]
  sorry

theorem nested_for_a
  (s : Proxy x' x b' b m a')
  (f : b -> Proxy x' x c' c m b')
  (g : c -> Proxy x' x d' d m c') :
  -- Proxy.forP s (fun a => Proxy.forP (f a) g) = Proxy.forP (Proxy.forP s f) g := by
  (s //> (f />/ g)) = ((s //> f) //> g) := by
  sorry

theorem nested_for_b
  (s : Proxy x' x b' b m a')
  (f : b -> Proxy x' x c' c m b')
  (g : c -> Proxy x' x d' d m c') :
  -- Proxy.forP (Proxy.forP s f) g = Proxy.forP s (f />/ g) := by
  ((s //> f) //> g) = (s //> (f />/ g)) := by
  rw [nested_for_a]

--------------------------

-- Definition repeatM `{Monad m} `(x : m a) : Producer' a m r :=
--   fun _ _ => lift x >~ cat (n:=n) (d:=d).
--
-- replicateM :: Monad m => Int -> m a -> Producer' a m ()
-- replicateM n m = lift m >~ take n

@[inline] def Proxy.drain (n : Nat) (d : r) : Consumer a m r :=
  Proxy.forP (Proxy.cat d n) (fun _ => Proxy.Pure ())

@[inline] def Pipe.map (n : Nat) (d : r) (f : a → b) : Pipe a b m r :=
  Proxy.forP (Proxy.cat d n) (fun val => Proxy.yield (f val))

@[inline] partial def Proxy.mapM [Inhabited r] (f : a -> m b) : Pipe a b m r :=
  .Request () (fun a => .M (f a) (fun b => .Respond b (fun _ => Proxy.mapM f)))

-- sequence :: Monad m => Pipe (m a) a m r
-- sequence = mapM id

@[inline] def mapFoldable (n : Nat) (d : r) (f : a → List b) : Pipe a b m r :=
  Proxy.forP (Proxy.cat d n) (fun x => (f x).forM Proxy.respond)

@[inline] def Pipe.whenP (cond : Bool) (action : Pipe a a m PUnit) : Pipe a a m PUnit :=
  if cond then action else Proxy.Pure ⟨⟩

def filter (n : Nat) (d : r) (p : a → Bool) : Pipe a a m r :=
  Proxy.forP (Proxy.cat d n) (fun x => Pipe.whenP (p x) (Proxy.yield x))

-- NOTE: coq uses `Proxy.forP` version
-- TODO: prove termination_by
@[inline] partial def Proxy.filter_unbounded [Inhabited r] (p : a -> Bool) : Pipe a a m r :=
  .Request () (fun a =>
    if p a then .Respond a (fun _ => Proxy.filter_unbounded p)
    else Proxy.filter_unbounded p)

@[inline] partial def Proxy.filterM [Inhabited r] (p : a -> m Bool) : Pipe a a m r :=
  sorry

@[inline] def Proxy.take : Nat -> Pipe a a m Unit
  | 0 => .Pure ()
  | n+1 => .Request () (fun a => .Respond a (fun _ => Proxy.take n))

@[inline] def takeWhile (p : a → Bool) (current_fuel : Nat) (default_r : r) : Pipe a a m Unit :=
  match current_fuel with
  | 0 => Proxy.Pure ()
  | Nat.succ fuel' =>
    Proxy.request () >>= fun a_val =>
    if p a_val
    then Proxy.yield a_val >>= fun _ => takeWhile p fuel' default_r
    else Proxy.Pure ⟨⟩

@[inline] def Proxy.replicateP_ (n : Nat) (act : Pipe a a m PUnit) : Pipe a a m PUnit :=
  match n with
  | 0 => Proxy.Pure ()
  | n'+1 => act >>= fun _ => replicateP_ n' act

@[inline] def Proxy.drop (n_to_drop : Nat) (initial_n_for_cat : Nat) (d : r) : Pipe a a m r :=
  (Proxy.replicateP_ n_to_drop (Proxy.request () >>= fun _ => .Pure ())) >>= fun _ => Proxy.cat d initial_n_for_cat

@[inline] def Proxy.drop_unbounded : Nat -> Pipe a a m Unit
  | 0 => Proxy.cat_unbounded
  | n+1 => .Request () (fun _ => Proxy.drop_unbounded n)

def concat (n : Nat) (d : r) : Pipe (List a) a m r :=
  Proxy.forP (Proxy.cat d n) (·.forM Proxy.respond)

private def findIndices.go (p : a → Bool) (initial_n : Nat) (current_fuel : Nat) (d : r) (i : Nat) : Pipe a Nat m r :=
  match current_fuel with
  | 0 => Proxy.Pure d
  | Nat.succ current_fuel' =>
    Proxy.await >>= fun a_val =>
    (if p a_val then Proxy.yield i >>= fun _ => Proxy.Pure () else Proxy.Pure ()) >>= fun _ =>
    go p initial_n current_fuel' d (i + 1)

def findIndices (p : a → Bool) (initial_n : Nat) (d : r) : Pipe a Nat m r :=
  findIndices.go p initial_n initial_n d 0

def elemIndices [BEq a] (x_val : a) (initial_n : Nat) (d : r) : Pipe a Nat m r :=
  findIndices (fun y => y == x_val) initial_n d

def scan (step : x → a → x) (begin_val : x) (done : x → b) (initial_n : Nat) (d : r) : Pipe a b m r :=
  let rec loop (current_x : x) (current_fuel : Nat) : Pipe a b m r :=
    match current_fuel with
    | 0 => Proxy.Pure d
    | Nat.succ current_fuel' =>
      Proxy.yield (done current_x) >>= fun _ =>
      Proxy.await >>= fun a_val =>
      let new_x := step current_x a_val
      loop new_x current_fuel'
  loop begin_val initial_n

@[inline] partial def Proxy.scan_unbounded [Inhabited r] (step : s → a → s) (acc : s) : Pipe a s m r :=
  .Request () (fun a =>
    let new_acc := step acc a
    .Respond new_acc (fun _ => scan_unbounded step new_acc))

-- scanM :: Monad m => (x -> a -> m x) -> m x -> (x -> m b) -> Pipe a b m r
-- scanM step begin done = do
--     x <- lift begin
--     loop x
--   where
--     loop x = do
--         b <- lift (done x)
--         yield b
--         a  <- await
--         x' <- lift (step x a)
--         loop $! x'
--
-- chain :: Monad m => (a -> m ()) -> Pipe a a m r
-- chain f = for cat $ \a -> do
--     lift (f a)
--     yield a

-- def fold [Monad m] (step : x → a → x) (begin_val : x) (done : x → b) (p0 : Producer a m Unit) : m b :=
--   let rec loop (p : Producer a m Unit) (current_x : x) : m b :=
--     match Proxy.next p with
--     | ProxyNextStep.Respond op cont => op >>= fun (val_opt, _) =>
--       match val_opt with
--       | .some a_val => loop (cont ⟨⟩) (step current_x a_val)
--       | .none => pure (done current_x) -- Should not happen for Respond
--     | ProxyNextStep.Pure _ => pure (done current_x)
--   loop p0 begin_val

-- `fold'` definition: `fold' (step : x -> a -> x) (begin : x) (done : x -> b) (p0 : Producer a m r) : m (b * r)%type`.
def fold' (step : x → a → x) (begin_val : x) (done : x → b) (p0 : Producer a m r) : m (b × r) :=
  let rec loop (p : Producer a m r) (current_x : x) : m (b × r) :=
    (Proxy.next p) >>= fun next_step =>
    match next_step with
    | ProxyNextStep.Respond op cont => op >>= fun (val_opt, _) =>
      match val_opt with
      | .some a_val => loop (cont ⟨⟩) (step current_x a_val)
      | .none => pure (done current_x, default) -- Default needs to be provided for r, or use Inhabited r
    | ProxyNextStep.Pure r_val => pure (done current_x, r_val)
  loop p0 begin_val

@[inline] def Proxy.fromList : List a → Producer a m Unit
| []      => .Pure ()
| (x::xs) => .Respond x (fun _ => fromList xs)

@[inline] def Proxy.fromArray : Array a -> Producer a m Unit :=
  fromList ∘ Array.toList

@[inline] partial def Proxy.enumerate.go [Inhabited r] (i : Nat) : Pipe a (Nat × a) m r :=
  .Request () (fun a => .Respond (i, a) (fun _ => go (i + 1)))

@[inline] def Proxy.enumerate [Inhabited r] : Pipe a (Nat × a) m r := Proxy.enumerate.go 0

@[inline] partial def Proxy.mapPipe (f : a → b) : Pipe a b m Unit :=
  .Request () (fun a => .Respond (f a) (fun _ => Proxy.mapPipe f))

@[inline] partial def Proxy.print [ToString a] [MonadLift IO m] [Inhabited r] : Pipe a a m r :=
  .Request () (fun a =>
    .M (MonadLift.monadLift (IO.println (toString a))) (fun _ =>
      .Respond a (fun _ => Proxy.print)))

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

-- `fold` definition: `fold (fun n _ => n + 1) 0 id (p0 : Producer a m unit) : m b`.
-- `Producer a m Unit` is `Proxy Empty Unit Unit a m Unit`.
def fold (step : x → a → x) (begin_val : x) (done : x → b) (p0 : Producer a m Unit) : m b :=
  let rec loop (p : Producer a m Unit) (current_x : x) : m b :=
    (Proxy.next p) >>= fun next_step =>
    match next_step with
    | ProxyNextStep.Respond op cont => op >>= fun (val_opt, _) =>
      match val_opt with
      | .some a_val => loop (cont ⟨⟩) (step current_x a_val)
      | .none => pure (done current_x) -- Should not happen for Respond
    | ProxyNextStep.Pure _ => pure (done current_x)
  loop p0 begin_val

-- `fold'` definition: `fold' (step : x -> a -> x) (begin : x) (done : x -> b) (p0 : Producer a m r) : m (b * r)%type`.
def fold' (step : x → a → x) (begin_val : x) (done : x → b) (p0 : Producer a m r) : m (b × r) :=
  let rec loop (p : Producer a m r) (current_x : x) : m (b × r) :=
    (Proxy.next p) >>= fun next_step =>
    match next_step with
    | ProxyNextStep.Respond op cont => op >>= fun (val_opt, _) =>
      match val_opt with
      | .some a_val => loop (cont ⟨⟩) (step current_x a_val)
      | .none => pure (done current_x, default) -- Default needs to be provided for r, or use Inhabited r
    | ProxyNextStep.Pure r_val => pure (done current_x, r_val)
  loop p0 begin_val

-- `foldM` definition: `foldM (step : x -> a -> m x) (begin : m x) (done : x -> m b) (p0 : Producer a m unit) : m b`.
def foldM (step : x → a → m x) (begin_m_x : m x) (done : x → m b) (p0 : Producer a m Unit) : m b :=
  let rec loop (p : Producer a m Unit) (current_x : x) : m b :=
    (Proxy.next p) >>= fun next_step =>
    match next_step with
    | ProxyNextStep.Respond op cont => op >>= fun (val_opt, _) =>
      match val_opt with
      | .some a_val => step current_x a_val >>= fun x' => loop (cont ⟨⟩) x'
      | .none => done current_x -- Should not happen
    | ProxyNextStep.Pure _ => done current_x
  begin_m_x >>= fun x0 => loop p0 x0

-- `foldM'` definition: `foldM' (step : x -> a -> m x) (begin : m x) (done : x -> m b) (p0 : Producer a m r) : m (b * r)%type`.
def foldM' (step : x → a → m x) (begin_m_x : m x) (done : x → m b) (p0 : Producer a m r) : m (b × r) :=
  let rec loop (p : Producer a m r) (current_x : x) : m (b × r) :=
    (Proxy.next p) >>= fun next_step =>
    match next_step with
    | ProxyNextStep.Respond op cont => op >>= fun (val_opt, _) =>
      match val_opt with
      | .some a_val => step current_x a_val >>= fun x' => loop (cont ⟨⟩) x'
      | .none => done current_x >>= fun b_val => pure (b_val, default) -- Default needs to be provided for r, or use Inhabited r
    | ProxyNextStep.Pure r_val => done current_x >>= fun b_val => pure (b_val, r_val)
  begin_m_x >>= fun x0 => loop p0 x0

-- `null` definition: `null (p : Producer a m unit) : m bool := x <-- next p ;; return_ $ match x with ...`.
def null (p : Producer a m Unit) : m Bool :=
  (Proxy.next p) >>= fun next_step =>
  match next_step with
  | ProxyNextStep.Respond _ _ => pure false
  | ProxyNextStep.Pure _ => pure true

-- `all` definition: `all (p : a -> bool) (p0 : Producer a m unit) : m bool := null $ p0 >-> (filter (fun a => ~~ (p a)) >> return_ tt).`
def all (n : Nat) (d : r) (p : a → Bool) (p0 : Producer a m Unit) : m Bool :=
  let negated_p := fun x_val => ¬ (p x_val)
  null (Proxy.connect (fun _ => p0) (filter n d negated_p >>= fun _ => Proxy.Pure ⟨⟩))

-- `any` definition: `any (p : a -> bool) (p0 : Producer a m unit) : m bool := fmap negb $ null $ p0 >-> (filter p >> return_ tt).`
def any (n : Nat) (d : r) (p : a → Bool) (p0 : Producer a m Unit) : m Bool :=
  not <$> (null (Proxy.connect (fun _ => p0) (filter n d p >>= fun _ => Proxy.Pure ⟨⟩)))

-- `and` definition: `and : Producer bool m unit -> m bool := all id.`
def and (n : Nat) (d : r) (p0 : Producer Bool m Unit) : m Bool :=
  all n d id p0

-- `or` definition: `or : Producer bool m unit -> m bool := any id.`
def or (n : Nat) (d : r) (p0 : Producer Bool m Unit) : m Bool :=
  any n d id p0

-- `elem` definition: `elem {a : eqType} (x : a) : Producer a m unit -> m bool := any (eq_op x).`
def elem [DecidableEq a] (n : Nat) (d : r) (x_val : a) (p0 : Producer a m Unit) : m Bool :=
  any n d (fun y => y == x_val) p0

-- `notElem` definition: `notElem {a : eqType} (x : a) : Producer a m unit -> m bool := all (negb \o eq_op x).`
def notElem [DecidableEq a] (n : Nat) (d : r) (x_val : a) (p0 : Producer a m Unit) : m Bool :=
  all n d (fun y => ¬ (y == x_val)) p0

-- `head` definition: `head (p : Producer a m unit) : m (Maybe a) := x <-- next p ;; return_ $ match x with ...`.
def head (p : Producer a m Unit) : m (Option a) :=
  (Proxy.next p) >>= fun next_step =>
  match next_step with
  | ProxyNextStep.Respond op _ => op >>= fun (val_opt, _) => pure val_opt
  | ProxyNextStep.Pure _ => pure .none

-- `find` definition: `find (p : a -> bool) (p0 : Producer a m unit) : m (Maybe a) := head (p0 >-> (filter p >> return_ tt)).`
def find (n : Nat) (d : r) (p : a → Bool) (p0 : Producer a m Unit) : m (Option a) :=
  head (Proxy.connect (fun _ => p0) (filter n d p >>= fun _ => Proxy.Pure ⟨⟩))

-- `findIndex` definition: `findIndex (p : a -> bool) (p0 : Producer a m unit) : m (Maybe nat) := head (p0 >-> (findIndices p >> return_ tt)).`
def findIndex (n : Nat) (d : r) (p : a → Bool) (p0 : Producer a m Unit) : m (Option Nat) :=
  head (Proxy.connect (fun _ => p0) (findIndices n d p >>= fun _ => Proxy.Pure ⟨⟩))

-- `index` definition: `index (n : nat) (p : Producer a m unit) : m (Maybe a) := head (p >-> (drop n >> return_ tt)).`
def index (n_idx : Nat) (n_pipe : Nat) (d : r) (p0 : Producer a m Unit) : m (Option a) :=
  head (Proxy.connect (fun _ => p0) (drop n_idx n_pipe d >>= fun _ => Proxy.Pure ⟨⟩))

-- `last` definition: `last (p0 : Producer a m unit) : m (Maybe a) := ...`
-- Coq's `last` passes `n` (from `Bounded.n`) to the loop.
def last (n : Nat) (p0 : Producer a m Unit) : m (Option a) :=
  let rec loop (z : Option a) (p_curr : Producer a m Unit) (fuel : Nat) : m (Option a) :=
    match fuel with
    | 0 => pure z -- Stream exhausted, return last accumulated `z`
    | Nat.succ fuel' =>
      (Proxy.next p_curr) >>= fun next_step =>
      match next_step with
      | ProxyNextStep.Respond op cont =>
        op >>= fun (val_opt, _) =>
        match val_opt with
        | .some a_val => loop (.some a_val) (cont ⟨⟩) fuel'
        | .none => pure z -- Should not happen for `Respond` as it produces a value
      | ProxyNextStep.Pure _ => pure z -- Producer finished before fuel runs out.

  (Proxy.next p0) >>= fun next_step_initial =>
  match next_step_initial with
  | ProxyNextStep.Respond op cont =>
    op >>= fun (val_opt, _) =>
    match val_opt with
    | .some a_val => loop (.some a_val) (cont ⟨⟩) n -- Start loop with first value and `Bounded.n` fuel
    | .none => pure .none
  | ProxyNextStep.Pure _ => pure .none

-- `length` definition: `fold (fun n _ => n + 1) 0 id.`
def length (p0 : Producer a m Unit) : m Nat :=
  fold (fun (n_val : Nat) (_ : a) => n_val + 1) 0 id p0

-- `maximum` definition: `fold step Nothing id.`
def maximum [Inhabited Nat] (p0 : Producer Nat m Unit) : m (Option Nat) :=
  let step (x_opt : Option Nat) (z : Nat) :=
    match x_opt with
    | .none => .some z
    | .some a' => .some (max a' z)
  fold step .none id p0

-- `minimum` definition: `fold step Nothing id.`
def minimum [Inhabited Nat] (p0 : Producer Nat m Unit) : m (Option Nat) :=
  let step (x_opt : Option Nat) (z : Nat) :=
    match x_opt with
    | .none => .some z
    | .some a' => .some (min a' z)
  fold step .none id p0

-- `sum` definition: `fold plus 0 id.`
def sum (p0 : Producer Nat m Unit) : m Nat :=
  fold Nat.add 0 id p0

-- `product` definition: `fold mult 1 id.`
def product (p0 : Producer Nat m Unit) : m Nat :=
  fold Nat.mul 1 id p0

-- `toList` (for `Producer a id unit`). `id` is `Id` monad in Lean.
def toList (p : Producer a Id Unit) : List a :=
  match p with
  | Proxy.Request v _ => Empty.elim v
  | Proxy.Respond a_val fu => a_val :: toList (fu ⟨⟩)
  | Proxy.M mx k => toList (k (Id.run mx))
  | Proxy.Pure _ => []

-- `toListM_fold` definition: `toListM_fold (p : Producer a m unit) : m (seq a) := ... fold step begin done.`
def toListM_fold (p : Producer a m Unit) : m (List a) :=
  let step (acc_fn : List a → List a) (x_val : a) := (acc_fn ∘ (fun l => x_val :: l))
  let begin_val : List a → List a := id
  let done (acc_fn : List a → List a) := acc_fn []
  fold step begin_val done p

-- `toListM` definition (recursive): `toListM (p : Producer a m unit) : m (seq a) := ...`
def toListM (p : Producer a m Unit) : m (List a) :=
  (Proxy.next p) >>= fun next_step =>
  match next_step with
  | ProxyNextStep.Respond op cont => op >>= fun (val_opt, _) =>
    match val_opt with
    | .some x_val => List.cons x_val <$> toListM (cont ⟨⟩)
    | .none => pure [] -- Should not happen for `Respond`
  | ProxyNextStep.Pure _ => pure []

--------------------------------------------------------------------------------
-- Theorems from PipesLawsPrelude
--------------------------------------------------------------------------------

-- Helper lemma: `s //> Proxy.respond = s` for general `Proxy` types.
-- This was `for_yield_general_corrected` from previous session.
lemma for_yield_general {x' x b' b r : Type u} (s : Proxy x' x PUnit b m r) :
  s //> (Proxy.respond : b → Proxy x' x PUnit b m PUnit) = s := by
  induction s generalizing x' x b m with
  | Request xa' k ih =>
    simp only [forP, Proxy.respond]
    congr
    funext a_val
    exact ih a_val
  | Respond xb k ih =>
    simp only [forP, Proxy.respond, Bind.bind]
    -- `(Proxy.respond xb)` is `Proxy.Respond xb (Proxy.Pure ⟨⟩)`.
    -- Applying `Bind.bind` rule for `Respond`:
    -- `Proxy.Respond xb (fun b_res => (Proxy.Pure ⟨⟩) >>= (fun (_ : PUnit) => (k b_res).forP (Proxy.respond)))`.
    -- `(Proxy.Pure ⟨⟩) >>= F` simplifies to `F ⟨⟩` by `Proxy.bind_pure_arg_PUnit`.
    -- So `(k b_res).forP (Proxy.respond)` where `b_res` is `PUnit`. This is `(k ⟨⟩).forP (Proxy.respond)`.
    -- By induction hypothesis `ih (k ⟨⟩)`, this is `k ⟨⟩`.
    -- So the entire LHS is `Proxy.Respond xb (fun b_arg => k ⟨⟩)`.
    -- Since `k` is `PUnit → Proxy ...`, `k ⟨⟩` is equivalent to `k` when applied to `PUnit`.
    exact rfl
  | M mx k ih =>
    simp only [forP, Proxy.respond]
    congr
    funext x_val
    exact ih x_val
  | Pure xr =>
    simp only [forP, Proxy.respond]
    rfl

-- Coq `map_id : forall a, map (n:=n) (d:=d) (@id a) = cat (n:=n) (d:=d).`
theorem map_id (n : Nat) (d : r) :
  map n d (fun x : a => x) = Proxy.cat d n := by
  simp only [map, Proxy.forP, Proxy.cat, Pipe.yield]
  -- Goal: `Proxy.forP (Proxy.pull d n ()) (fun val => Proxy.respond val) = Proxy.pull d n ()`
  -- The `Proxy.pull d n ()` is `Pipe a a m r`, which is `Proxy Unit a Unit a m r`.
  -- The function `(fun val => Proxy.respond val)` is `a → Proxy Unit a Unit a m Unit`.
  -- This matches the type requirements for `for_yield_general` where `x'=Unit, x=a, b'=Unit, b=a`.
  apply for_yield_general

-- Coq `map_compose `{MonadLaws m} : forall `(f : a -> b) `(g : b -> c), map (n:=n) (d:=d) (g \o f) = map (n:=n) (d:=d) f >-> map (n:=n) (d:=d) g.`
theorem map_compose (n : Nat) (d : r) (f : a → b) (g : b → c) :
  map n d (g ∘ f) = map n d f >-> map n d g := by
  simp only [map, Proxy.forP, Proxy.cat, Pipe.yield, Proxy.connect]
  -- This theorem is typically quite involved, relying on distributivity and associativity laws
  -- for `Proxy.forP`, `Proxy.pullR` (`+>>`), and `Bind.bind`.
  -- It's essentially an associativity law for the `Pipe` category composition.
  -- The Coq proof hints at `respond_distrib` and `reduce_proxy`.
  -- Let's re-use `PipesLaws.nested_for_a` (which is `forP` associativity).
  -- LHS: `Proxy.forP (Proxy.cat d n) (fun val => Pipe.yield (g (f val)))`
  -- RHS: `Proxy.pullR (fun _ => Proxy.forP (Proxy.cat d n) (fun val => Pipe.yield (f val))) (Proxy.forP (Proxy.cat d n) (fun val => Pipe.yield (g val)))`
  -- This requires relating `Proxy.forP` and `Proxy.pullR`.
  -- This theorem likely relies on a deeper category theory interpretation of Pipes.
  sorry

-- `toListM_each_id` definition: `toListM \o (fun xs => each (x':=False) (x:=unit) xs) =1 pure (a:=seq a).`
-- The `each` in Coq is `Proxy.each` from `Pipes.Core` (the one specialized for `Producer`).
-- So `(fun xs => Proxy.each xs)` means `List a -> Producer a m Unit`.
theorem toListM_each_id {a : Type u} (xs : List a) :
  toListM (Proxy.each xs) = pure xs := by
  induction xs generalizing m with
  | nil =>
    simp only [Proxy.each, Proxy.fromList, toListM]
  | cons x' xs' ih =>
    simp only [Proxy.each, Proxy.fromList, toListM, Functor.map_pure, List.cons.injEq]
    -- Goal: `(Proxy.next (Proxy.Respond x' (fun _ => Proxy.fromList xs'))) >>= (fun next_step => ...)`
    -- `Proxy.next (.Respond x' k)` is `ProxyNextStep.Respond (pure (some x', ())) (fun _ => Proxy.next (k ⟨⟩))`
    -- So `op` is `pure (some x', ())`.
    -- `op >>= fun (val_opt, _) => ...` becomes `pure (some x') >>= fun val_opt => ...`
    -- `pure (some x') >>= (fun val_opt => match val_opt with ...)` simplifies to
    -- `match some x' with | .some x_val => List.cons x_val <$> toListM (cont ⟨⟩) | .none => pure []`
    -- This is `List.cons x' <$> toListM (Proxy.fromList xs')`.
    -- By induction hypothesis `ih`: `toListM (Proxy.fromList xs') = pure xs'`.
    rw [ih]
    rfl

end PipesLawsPrelude
