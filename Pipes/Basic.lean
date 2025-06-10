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

@[inline, simp] abbrev Proxy.map (f : r → s) (p : Proxy a' a b' b m r) : Proxy a' a b' b m s :=
  Proxy.bind p (Proxy.Pure ∘ f)

@[inline, simp] abbrev Proxy.seq (pf : Proxy a' a b' b m (r → s)) (px : Unit → Proxy a' a b' b m r) : Proxy a' a b' b m s :=
  Proxy.bind pf (fun f => Proxy.map f (px ()))

@[inline, simp] abbrev Proxy.monadLift (mx : m r) : Proxy a' a b' b m r :=
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
    | Request a' k ih => simp [Functor.map, Proxy.map]; funext a; exact ih a
    | Respond b k ih => simp [Functor.map, Proxy.map]; funext b'; exact ih b'
    | M mx k ih => simp [Functor.map, Proxy.map]; funext x; exact ih x
    | Pure r => rfl
  )
  (pure_bind := by intro α β x f; rfl)
  (bind_assoc := by
    intro α β γ x f g
    induction x with
    | Request a' k ih => simp [Bind.bind, Proxy.bind]; funext a; exact ih a;
    | Respond b k ih => simp [Bind.bind, Proxy.bind]; funext b'; exact ih b';
    | M mx k ih => simp [Bind.bind, Proxy.bind]; funext x; exact ih x;
    | Pure r => rfl
  )

instance : LawfulApplicative (Proxy a' a b' b m) := inferInstance
instance : LawfulFunctor (Proxy a' a b' b m) := inferInstance

@[inline] instance [MonadState σ m] : MonadState σ (Proxy a' a b' b m) where
  get := Proxy.monadLift MonadState.get
  set := Proxy.monadLift ∘ MonadState.set
  modifyGet := Proxy.monadLift ∘ MonadState.modifyGet

@[inline] instance [MonadReader ρ m] : MonadReader ρ (Proxy a' a b' b m) where
  read := Proxy.monadLift MonadReader.read

@[always_inline, inline] def Proxy.runEffect [Monad m] (eff : Proxy Empty a b' Empty m r) : m r :=
  match eff with
    | .Request x _ => Empty.elim x
    | .Respond x _ => Empty.elim x
    | .M mx k      => mx >>= fun x => Proxy.runEffect (k x)
    | .Pure xr     => pure xr
  termination_by structural eff

@[inline, simp] def Proxy.respond (xb : b) : Proxy a' a b' b m b' :=
  Proxy.Respond xb Proxy.Pure

@[inline, simp] def Proxy.forP
  (p0 : Proxy x' x b' b m a')
  (fb : b → Proxy x' x c' c m b') :
  Proxy x' x c' c m a' :=
  match p0 with
  | .Request xa' k => .Request xa' (fun a => (k a).forP fb)
  | .Respond xb k => (fb xb).bind (fun b' => (k b').forP fb)
  | .M mx k => .M mx (fun x => (k x).forP fb)
  | .Pure xa' => .Pure xa'

infixl:60 " //> " => Proxy.forP

infixl:60 " />/ " => fun f g a => f a //> g

-- Backward composition (request category)

@[inline, simp] abbrev Proxy.request (xa' : a') : Proxy a' a b' b m a :=
  Proxy.Request xa' Proxy.Pure

@[inline, simp] def Proxy.rofP
  (fb' : b' → Proxy a' a y' y m b)
  (p0 : Proxy b' b y' y m c) :
  Proxy a' a y' y m c :=
  match p0 with
  | .Request xb' k => (fb' xb').bind (fun b => (k b).rofP fb')
  | .Respond xy k => .Respond xy (fun y' => (k y').rofP fb')
  | .M mx k => .M mx (fun x => (k x).rofP fb')
  | .Pure xc => .Pure xc

infixl:60 " >\\\\ " => Proxy.rofP

infixl:60 " \\>\\ " => fun f g a => f >\\ g a

-- TODO: prove https://hackage.haskell.org/package/pipes-4.3.16/docs/src/Pipes.Core.html#push
@[inline] partial def Proxy.push [Inhabited r] : a -> Proxy a' a a' a m r :=
  (.Respond · (.Request · (Proxy.push)))

private inductive ProxyPushRWF (a' a b' b c' c m r) where
  | go : (b' → Proxy a' a b' b m r) → Proxy b' b c' c m r → ProxyPushRWF a' a b' b c' c m r
  | reg : Proxy a' a b' b m r → ProxyPushRWF a' a b' b c' c m r

private inductive ProxyPushRWFRel :
    ProxyPushRWF a' a b' b c' c m r → ProxyPushRWF a' a b' b c' c m r → Prop where
  | go_request : ProxyPushRWFRel (.reg (k xb')) (.go k (.Request xb' _kb))
  | go_respond : ProxyPushRWFRel (.go k (kc' yc)) (.go k (.Respond xc kc'))
  | go_m : ProxyPushRWFRel (.go k (kx x)) (.go k (.M mx kx))
  | request : ProxyPushRWFRel (.reg (k a)) (.reg (.Request xa' k))
  | m : ProxyPushRWFRel (.reg (k x)) (.reg (.M mx k))
  | respond : ProxyPushRWFRel (.go k t) (.reg (.Respond xb k))

private instance : WellFoundedRelation (ProxyPushRWF a' a b' b c' c m r) where
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
  @[inline] def Proxy.pushR.go' [Inhabited r]
    (fb : b → Proxy b' b c' c m r)
    (k : b' → Proxy a' a b' b m r)
    (p : Proxy b' b c' c m r)
    : Proxy a' a c' c m r :=
    match p with
    | .Request xb' _kb => Proxy.pushR fb (k xb')
    | .Respond xc kc' => .Respond xc (fun c' => Proxy.pushR.go' fb k (kc' c'))
    | .M mx kx => .M mx (fun x => Proxy.pushR.go' fb k (kx x))
    | .Pure xr => .Pure xr
    termination_by ProxyPushRWF.go k p
    decreasing_by all_goals constructor

  @[inline] def Proxy.pushR [Inhabited r]
    (fb : b → Proxy b' b c' c m r)
    (p0 : Proxy a' a b' b m r) :
    Proxy a' a c' c m r :=
    match p0 with
    | .Request xa' k => .Request xa' (fun a => Proxy.pushR fb (k a))
    | .Respond xb k => Proxy.pushR.go' fb k (fb xb)
    | .M mx k => .M mx (fun x => Proxy.pushR fb (k x))
    | .Pure xr => .Pure xr
    termination_by (.reg p0 : ProxyPushRWF a' a b' b c' c m r)
    decreasing_by all_goals constructor
end

infixl:60 " >>~ " => fun x y => Proxy.pushR y x

infixl:60 " >~> " => fun f g a => f a >>~ g

@[inline] partial def Proxy.pull [Inhabited r] : a' -> Proxy a' a a' a m r :=
  (.Request · (.Respond · Proxy.pull))

private inductive ProxyPullRWF (a' a b' b c' c m r) where
  | go : (b → Proxy b' b c' c m r) → Proxy a' a b' b m r → ProxyPullRWF a' a b' b c' c m r
  | reg : Proxy b' b c' c m r → ProxyPullRWF a' a b' b c' c m r

private inductive ProxyPullRWFRel :
    ProxyPullRWF a' a b' b c' c m r → ProxyPullRWF a' a b' b c' c m r → Prop where
  | go_request : ProxyPullRWFRel (.go k (kc' yc)) (.go k (.Request xc kc'))
  | go_respond : ProxyPullRWFRel (.reg (k xb')) (.go k (.Respond xb' _kb))
  | go_m : ProxyPullRWFRel (.go k (kx x)) (.go k (.M mx kx))
  | request : ProxyPullRWFRel (.go k t) (.reg (.Request xb k))
  | respond : ProxyPullRWFRel (.reg (k a)) (.reg (.Respond xa' k))
  | m : ProxyPullRWFRel (.reg (k x)) (.reg (.M mx k))

private instance : WellFoundedRelation (ProxyPullRWF a' a b' b c' c m r) where
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
  @[inline] def Proxy.pullR.go' [Inhabited r]
    (fb' : b' → Proxy a' a b' b m r)
    (k : b → Proxy b' b c' c m r)
    (p : Proxy a' a b' b m r) :
    Proxy a' a c' c m r :=
    match p with
    | .Request xa' ka => .Request xa' (fun a => Proxy.pullR.go' fb' k (ka a))
    | .Respond xb _kb' => (k xb).pullR fb'
    | .M mx kx => .M mx (fun x => Proxy.pullR.go' fb' k (kx x))
    | .Pure xr => .Pure xr
    termination_by ProxyPullRWF.go k p
    decreasing_by all_goals constructor

  @[inline] def Proxy.pullR [Inhabited r]
    (fb' : b' → Proxy a' a b' b m r)
    (p0 : Proxy b' b c' c m r) :
    Proxy a' a c' c m r :=
    match p0 with
    | .Request xb' k => Proxy.pullR.go' fb' k (fb' xb')
    | .Respond xc k => .Respond xc (fun c' => (k c').pullR fb')
    | .M mx k => .M mx (fun x => (k x).pullR fb')
    | .Pure xr => .Pure xr
    termination_by (.reg p0 : ProxyPullRWF a' a b' b c' c m r)
    decreasing_by all_goals constructor
end

infixl:60 " +>> " => Proxy.pullR

infixl:60 " >+> " => fun f g a => f +>> g a

-- Reflect operation (dual)
def Proxy.reflect (p : Proxy a' a b' b m r) : Proxy b b' a a' m r :=
  match p with
  | .Request xa' k => .Respond xa' (fun a => (k a).reflect)
  | .Respond xb k => .Request xb (fun b' => (k b').reflect)
  | .M mx k => .M mx (fun x => (k x).reflect)
  | .Pure xr => .Pure xr

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

notation:60 f " <\\\\ " g => g />/ f
notation:60 f " /</ " g => g \>\ f
notation:60 f " <~< " g => g >~> f
notation:60 f " <+< " g => g >+> f
notation:60 f " <// " x => x //> f
notation:60 x " //< " f => f >\\ x
notation:60 f " ~<< " x => x >>~ f
notation:60 x " <<+ " f => f +>> x

def Proxy.yield : b -> Producer b m Unit := Proxy.respond

def Proxy.await : Consumer a m a := Proxy.request ()

-- TODO: this is like an identity pipe, should not be partial
partial def Proxy.cat [Inhabited r] : Pipe a a m r :=
  .Request () (fun a => .Respond a (fun _ => Proxy.cat))

def Proxy.fromList : List a → Producer a m Unit
| []      => .Pure ()
| (x::xs) => .Respond x (fun _ => fromList xs)

def Proxy.fromArray : Array a -> Producer a m Unit :=
  fromList ∘ Array.toList

partial def Proxy.filter [Inhabited r] (p : a -> Bool) : Pipe a a m r :=
  .Request () (fun a =>
    if p a then .Respond a (fun _ => Proxy.filter p)
    else Proxy.filter p)

def Proxy.take : Nat -> Pipe a a m Unit
  | 0 => .Pure ()
  | n+1 => .Request () (fun a => .Respond a (fun _ => Proxy.take n))

def Proxy.drop : Nat -> Pipe a a m Unit
  | 0 => Proxy.cat
  | n+1 => .Request () (fun _ => Proxy.drop n)

partial def Proxy.enumerateGo [Inhabited r] (i : Nat) : Pipe a (Nat × a) m r :=
  .Request () (fun a => .Respond (i, a) (fun _ => Proxy.enumerateGo (i + 1)))

def Proxy.enumerate [Inhabited r] : Pipe a (Nat × a) m r := Proxy.enumerateGo 0

-- Map over a pipe
partial def Proxy.mapPipe (f : a → b) : Pipe a b m Unit :=
  .Request () (fun a => .Respond (f a) (fun _ => Proxy.mapPipe f))

partial def Proxy.scan [Inhabited r] (f : s → a → s) (acc : s) : Pipe a s m r :=
  .Request () (fun a =>
    let new_acc := f acc a
    .Respond new_acc (fun _ => Proxy.scan f new_acc))

-- For monadic effects
partial def Proxy.mapM [Inhabited r] (f : a -> m b) : Pipe a b m r :=
  .Request () (fun a => .M (f a) (fun b => .Respond b (fun _ => Proxy.mapM f)))

-- Print each element (for debugging)
partial def Proxy.print [ToString a] [MonadLift IO m] [Inhabited r] : Pipe a a m r :=
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

namespace ProxyLaws

universe u
variable (a' a b' b : Type u) (m : Type u -> Type u) -- [Monad m] [LawfulMonad m]

-- Respond Category
section RespondCategory

-- Respond distributivity theorem
theorem respondDistrib [Monad m] [LawfulMonad m] (f : a → Proxy x' x b' b m a')
                       (g : a' → Proxy x' x b' b m r)
                       (h : b → Proxy x' x c' c m b') :
  (f >=> g) />/ h = (f />/ h) >=> (g />/ h) := by
  funext a
  simp only [Bind.bind, (· >=> ·)]
  induction f a with
  | Pure a' =>
    simp_all only [Proxy.bind, Proxy.forP]
  | Respond b k ih =>
    simp only [Proxy.Respond, Proxy.bind, Proxy.forP, Proxy.rofP]
    simp_all only
    sorry
  | Request x' k ih =>
    simp [ih, Proxy.Respond, Proxy.bind, Proxy.forP]
  | M mx ih =>
    simp [*]

--    instance RespondCategory {x' x : Type u} :
--      CategoryTheory.Category (Type u × Type u) where
--      Hom A B := B.2 → Proxy x' x B.1 B.2 m A.1
--      id A := Proxy.respond
--      comp f g := g />/ f
--      id_comp := by
--        intro A B f
--        funext z
--        aesop?
--      comp_id := by
--        intro A B f
--        funext z
--        obtain ⟨fst, snd⟩ := A
--        obtain ⟨fst_1, snd_1⟩ := B
--        simp_all only
--        sorry
--      assoc := by
--        intro A B C D f g h
--        funext z
--        obtain ⟨fst, snd⟩ := A
--        obtain ⟨fst_1, snd_1⟩ := B
--        obtain ⟨fst_2, snd_2⟩ := C
--        obtain ⟨fst_3, snd_3⟩ := D
--        simp_all only
--        sorry

lemma respondZeroImpl (someR : r) (f : c → Proxy a' a b' b m r): Proxy.forP (.Pure someR) f = .Pure someR := by rfl

theorem respondZero  {a' a b' b c r : Type u} {m : Type u → Type u} (f : c → Proxy a' a b' b m r) :
  .Pure />/ f = .Pure := by
  rfl

end RespondCategory

section RequestCategory

theorem requestDistrib (f : c → Proxy b' b y' y m c')
                       (g : c' → Proxy b' b y' y m r)
                       (h : b' → Proxy a' a y' y m b) :
  h \>\ (f >=> g) = (h \>\ f) >=> (h \>\ g) := by
  funext x
  sorry

--instance RequestCategory {y' y : Type u} :
--  CategoryTheory.Category (Type u × Type u) where
--  Hom A B := A.1 → Proxy B.1 B.2 y' y m A.2
--  id A := Proxy.request
--  comp f g := f \>\ g
--  id_comp := by
--    intro A B f
--    funext z
--    aesop?
--  comp_id := by
--    intro A B f
--    funext z
--    obtain ⟨fst, snd⟩ := A
--    obtain ⟨fst_1, snd_1⟩ := B
--    simp_all only
--    sorry
--  assoc := by
--    intro A B C D f g h
--    funext z
--    obtain ⟨fst, snd⟩ := A
--    obtain ⟨fst_1, snd_1⟩ := B
--    obtain ⟨fst_2, snd_2⟩ := C
--    obtain ⟨fst_3, snd_3⟩ := D
--    simp_all only
--    sorry

lemma requestZeroImpl (someR : r) (f : c → Proxy a' a b' b m r): Proxy.rofP f (.Pure someR) = .Pure someR := by rfl

theorem requestZero (f : c → Proxy a' a b' b m r) :
  f \>\ .Pure = .Pure := by
  rfl

end RequestCategory

section PushCategory

theorem pushRequest [Inhabited r]
  (f : b → Proxy b' b c' c m r)
  (g : a → Proxy a' a b' b m r)
  (x : _) :
  Proxy.Request x g >>~ f = Proxy.Request x (g >~> f) := by
  sorry

theorem pushM [Inhabited r] (f : b → Proxy b' b c' c m r)
              (g : x → Proxy a' a b' b m r) (h : m x) :
  Proxy.M h g >>~ f = Proxy.M h (g >~> f) := by
  simp [Proxy.pushR]
  sorry

variable {n : ℕ} (hn : n > 0) {r : Type u} (d : r)

-- Push Category instance
-- instance PushCategory [Inhabited r] :
--   CategoryTheory.Category (Type u × Type u) where
--   Hom A B := B.2 → Proxy B.1 B.2 A.1 A.2 m r
--   id A := Proxy.push
--   comp f g := f >~> g
--   id_comp := by
--     intro A B f
--     funext z
--     simp [Proxy.pushRFunc, Proxy.push]
--     simp_all only [gt_iff_lt]
--     sorry
--   comp_id := by
--     intro A B f
--     funext z
--     simp [Proxy.pushRFunc, Proxy.push]
--     simp_all only [gt_iff_lt]
--     sorry
--   assoc := by
--     intro A B C D f g h
--     funext z
--     simp [Proxy.pushRFunc]
--     simp_all only [gt_iff_lt]
--     sorry

end PushCategory

-- Pull Category
section PullCategory

theorem pullRespond [Inhabited r] (f : b' → Proxy a' a b' b m r)
                   (g : c' → Proxy b' b c' c m r) (x : c) :
  f +>> Proxy.Respond x g = Proxy.Respond x (f >+> g) := by
  simp [Proxy.pullR]
  sorry

theorem pullM [Inhabited r] (f : b' → Proxy a' a b' b m r)
              (g : x → Proxy b' b c' c m r) (h : m x) :
  f +>> Proxy.M h g = Proxy.M h (f >+> g) := by
  simp [Proxy.pullR]
  sorry

-- instance PullCategory [Inhabited r] :
--   CategoryTheory.Category (Type u × Type u) where
--   Hom A B := A.1 → Proxy B.1 B.2 A.1 A.2 m r
--   id A := Proxy.pull
--   comp f g := f >+> g
--   id_comp := by
--     intro A B f
--     funext z
--     sorry
--   comp_id := by
--     intro A B f
--     funext z
--     obtain ⟨fst, snd⟩ := A
--     obtain ⟨fst_1, snd_1⟩ := B
--     simp_all only
--     sorry
--   assoc := by
--     intro A B C D f g h
--     funext z
--     obtain ⟨fst, snd⟩ := A
--     obtain ⟨fst_1, snd_1⟩ := B
--     obtain ⟨fst_2, snd_2⟩ := C
--     obtain ⟨fst_3, snd_3⟩ := D
--     simp_all only
--     sorry

theorem pushPullAssoc [Inhabited r]
  (f : b' → Proxy a' a b' b m r)
  (g : a → Proxy b' b c' c m r)
  (h : c → Proxy c' c b' b m r) :
  (f >+> g) >~> h = f >+> (g >~> h) := by
  funext x
  simp [Proxy.pushR]
  sorry

end PullCategory

section Duals

variable {a' a b' b r : Type u} {m : Type u → Type u}

theorem requestId : Proxy.reflect ∘ Proxy.request = @Proxy.respond a' a b' b m := by
  funext x
  simp [Proxy.reflect, Proxy.request, Proxy.respond]

theorem reflectDistrib (f : a → Proxy a' a b' b m r)
                       (g : r → Proxy a' a b' b m r) (x : a) :
  Proxy.reflect (f x >>= g) = Proxy.reflect (f x) >>= (Proxy.reflect ∘ g) := by
  sorry

theorem requestComp (f : a → Proxy a' a b' b m r)
                    (g : a → Proxy a r b' b m r) :
  Proxy.reflect ∘ (f \>\ g) = (Proxy.reflect ∘ g) />/ (Proxy.reflect ∘ f) := by
  simp [Proxy.bind, Proxy.reflect, Proxy.respond, Proxy.request, Proxy.rofP, Proxy.forP]
  funext x
  sorry

theorem respondId : Proxy.reflect ∘ Proxy.respond = @Proxy.request a' a b' b m := by
  funext x
  simp [Proxy.reflect, Proxy.respond, Proxy.request]

theorem respondComp (f : a → Proxy a' a b' b m r)
                    (g : b → Proxy a' a b' b m b') :
  Proxy.reflect ∘ (f />/ g) = (Proxy.reflect ∘ g) \>\ (Proxy.reflect ∘ f) := by
  funext x
  simp [Proxy.reflect, Proxy.forP, Proxy.rofP]
  induction (f x) with
  | Request a' k ih =>
    simp [Proxy.bind, Proxy.reflect]
    funext a
    exact ih a
  | Respond b k ih =>
    simp [Proxy.bind, Proxy.reflect, Proxy.respond, Proxy.request, Proxy.rofP, Proxy.forP]
    sorry
  | M mx k ih =>
    simp [Proxy.bind, Proxy.reflect]
    funext x
    exact ih x
  | Pure r =>
    simp [Proxy.bind, Proxy.reflect]

theorem distributivity (f : a → Proxy a' a b' b m r)
                       (g : r → Proxy a' a b' b m r) :
  Proxy.reflect ∘ (f >=> g) = (Proxy.reflect ∘ f) >=> (Proxy.reflect ∘ g) := by sorry -- reflectDistrib f g

theorem zeroLaw (x : r) : Proxy.reflect (pure x : Proxy a' a b' b m r) = (pure x : Proxy b b' a a' m r) := by
  simp [pure, Proxy.reflect]

theorem involution (p : Proxy a' a b' b m r) : Proxy.reflect (Proxy.reflect p) = p := by
  induction p with
  | Request xa' k ih =>
    simp [Proxy.reflect]
    funext a
    exact ih a
  | Respond xb k ih =>
    simp [Proxy.reflect]
    funext b'
    exact ih b'
  | M mx k ih =>
    simp [Proxy.reflect]
    funext x
    exact ih x
  | Pure xr =>
    simp [Proxy.reflect]

end Duals

end ProxyLaws
