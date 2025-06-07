/-
Free Monads for Less - Church Encoding in Lean 4

The Church-encoded free monad for a functor f.
It is asymptotically more efficient to use (>>=) for F than with regular Free.

Based on "Free Monads for Less" by Edward Kmett


Also check Zulip "Church-encoded free monad"
-/

import Aesop
import Init.Control.State
import Batteries.Control.AlternativeMonad

abbrev F' (f : Type u → Type u) (α : Type u) := ∀ {r : Type u}, (α → r) → (f r → r) → r

-- @[always_inline, inline] def F.runF (x : F f α) (kp : α → r) (kf : f r → r) : r := x kp kf

-- Church-encoded free monad
structure F (f : Type u → Type u) (α : Type u) : Type (u+1) where
  runF : ∀ {r : Type u}, (α → r) → (f r → r) → r

-- def F (f : Type u → Type u) (α : Type u) := ∀ {r : Type u}, (α → r) → (f r → r) → r ?

-- @[always_inline, inline] def F.runFExpl (x : F f α) (kp : α → r) (kf : f r → r) : r := @x.runF r kp kf
-- @[always_inline, inline] def F.runF (x : F f α) (kp : α → r) (kf : f r → r) : r := x kp kf

-- Functor map
@[inline, simp] def F.map [Functor f] (g : α → β) (m : F f α) : F f β := ⟨fun kp kf => m.runF (kp ∘ g) kf⟩
@[inline, simp] def F.pure (a : α) : F f α := ⟨fun kp _kf => kp a⟩
@[inline, simp] def F.bind (m : F f α) (f' : α → F f β) : F f β := ⟨fun kp kf => m.runF (fun a => (f' a).runF kp kf) kf⟩
@[inline, simp] def F.monadLift [Functor f] (fa : f α) : F f α := ⟨fun kp kf => kf (kp <$> fa)⟩
@[inline, simp] def F.foldF (pureF : α → r) (impureF : f r → r) (fa : F f α) : r := fa.runF pureF impureF

@[inline] instance [Functor f] : Functor (F f) := { map := F.map }
@[inline] instance : Pure (F f) := ⟨F.pure⟩
@[inline] instance : Bind (F f) := ⟨F.bind⟩
@[inline] instance : Monad (F f) := {}
@[inline] instance [Functor m] : MonadLift m (F m) := ⟨F.monadLift⟩

-- Retract for monadic computations
-- |
-- 'retract' is the left inverse of 'lift' and 'liftF'
--
-- @
-- 'retract' . 'lift' = 'id'
-- 'retract' . 'liftF' = 'id'
-- @

-- From https://github.com/leanprover-community/mathlib4/blob/730e4db21155a3faee9cadd55d244dbf72f06391/Mathlib/Control/Combinators.lean#L14-L17
@[always_inline, inline, simp] def Monad.joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α := bind a id

@[inline, simp] def F.retract [Monad m] : F m α → m α := fun m => m.runF Pure.pure Monad.joinM
-- Natural transformation lifting
@[inline, simp] def F.hoistF (nt : {α : Type u} → f α → g α) : F f α → F g α := fun m => ⟨fun kp kf => m.runF kp (kf ∘ nt)⟩
-- Monadic iteration
@[inline, simp] def F.iterM [Pure m] (phi : f (m α) → m α) : F f α → m α := fun xs => xs.runF Pure.pure phi

@[inline, simp]
def F.failure [Alternative f] : F f α := ⟨fun _kp kf => kf Alternative.failure⟩

@[inline, simp]
def F.orElse [Monad f] [Alternative f] (x : F f α) (y : (Unit -> F f α)) : F f α :=
  ⟨fun kp kf =>
    let try_x := x.runF (fun a => Pure.pure (kp a)) Monad.joinM
    let try_y := fun _ => (y ()).runF (fun a => Pure.pure (kp a)) Monad.joinM
    kf (Alternative.orElse try_x try_y)
  ⟩

-- TODO: use def like ReaderT, but <|> fails even with OrElse
-- @[inline] instance [Monad f] [Alternative f] : OrElse (F f a) := ⟨F.orElse⟩
-- @[inline] instance [Monad f] [Alternative f] : HOrElse (F f a) (F f a) (F f a) := ⟨F.orElse⟩

@[inline] instance [Monad f] [Alternative f] : Alternative (F f) := ⟨F.failure, F.orElse⟩
@[inline] instance [Monad f] [Alternative f] : AlternativeMonad (F f) where

namespace AlternativeTests

    -- Reusable runners
    def runFOption (m : F Option String) : Option String :=
      m.runF (some) (fun | none => none | some s => s)

    def runFString (m : F Option String) : String :=
      m.runF (fun x => s!"a->r {x}") (fun | none => "fr->r was none" | some s => s)

    -- Test with Option as the base functor
    def testF1 : F Option String := F.failure
    def testF2 : F Option String := F.pure "hello"
    def testF3 : F Option String := F.pure "world"

    #guard runFOption testF1 = none
    #guard runFOption testF2 = some "hello"
    #guard runFOption testF3 = some "world"

    #guard runFString testF1 = "fr->r was none"
    #guard runFString testF2 = "a->r hello"
    #guard runFString testF3 = "a->r world"

    -- Test Alternative operations
    def testOr12 : F Option String := testF1 <|> testF2  -- failure <|> pure "hello"
    def testOr21 : F Option String := testF2 <|> testF1  -- pure "hello" <|> failure
    def testOr23 : F Option String := testF2 <|> testF3  -- pure "hello" <|> pure "world"
    def testOr11 : F Option String := testF1 <|> testF1  -- failure <|> failure

    -- Let's see what actually happens:
    #guard runFOption testOr12 = some "hello"
    #guard runFOption testOr21 = some "hello"
    #guard runFOption testOr23 = some "hello"
    #guard runFOption testOr11 = none

    #guard runFString testOr12 = "a->r hello"
    #guard runFString testOr21 = "a->r hello"
    #guard runFString testOr23 = "a->r hello"
    #guard runFString testOr11 = "fr->r was none"

end AlternativeTests

-- MonadState instance
@[inline] instance [Functor m] [MonadState σ m] : MonadState σ (F m) where
  get := F.monadLift MonadState.get
  set s := F.monadLift (MonadState.set s)
  modifyGet f := F.monadLift (MonadState.modifyGet f)

-- MonadReader instance
@[inline] instance [Functor m] [MonadReader ρ m] : MonadReader ρ (F m) where
  read := F.monadLift MonadReader.read

-- MonadExcept instance
@[inline] instance [Functor m] [Monad m] [MonadExcept ε m] : MonadExcept ε (F m) where
  throw e := F.monadLift (MonadExcept.throw e)
  tryCatch m h := F.monadLift (tryCatch (F.retract m) (F.retract ∘ h))

instance : LawfulMonad (F f) := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

instance : LawfulApplicative (F f) := inferInstance
instance : LawfulFunctor (F f) := inferInstance

@[ext]
theorem F.ext
  (x y : F f α)
  (h : ∀ (r : Type u), (α → r) → (f r → r) → @x.runF r = @y.runF r) : x = y := by
    cases x; cases y
    simp_all only [mk.injEq]
    apply funext; intro r
    apply funext; intro kp
    apply funext; intro kf
    exact congrFun (congrFun (h r kp kf) kp) kf

instance [Monad f] [Alternative f] [LawfulAlternative f] [LawfulMonad f] : LawfulAlternative (F f) where
  map_failure g := by rfl
  failure_seq x := by rfl
  orElse_failure x := by
    apply F.ext
    intros r kp kf
    simp [F.orElse, F.failure, F.runF, Alternative.orElse, Alternative.failure, Monad.joinM]
    sorry

  -- failure <|> y = y
  failure_orElse y := by sorry

  -- (x <|> y) <|> z = x <|> (y <|> z)
  orElse_assoc x y z := by
    cases x; cases y; cases z
    sorry

  -- map g (x <|> y) = map g x <|> map g y
  map_orElse x y g := by
    cases x; cases y;
    sorry

-- Properties and theorems
namespace Properties

    -- Left identity: return a >>= f ≡ f a
    theorem bind_pure_left [Functor f] (a : α) (k : α → F f β) : (pure a : F f α) >>= k = k a := by rfl

    -- Right identity: m >>= return ≡ m
    theorem bind_pure_right [Functor f] (m : F f α) : m >>= pure = m := by rfl

    -- Associativity: (m >>= f) >>= g ≡ m >>= (λx. f x >>= g)
    theorem bind_assoc [Functor f] (m : F f α) (k₁ : α → F f β) (k₂ : β → F f γ) :
      (m >>= k₁) >>= k₂ = m >>= (fun x => k₁ x >>= k₂) := by rfl

    -- retract is left inverse of monadLift
    theorem retract_monadLift_id [Monad m] [LawfulMonad m] (ma : m α) :
      F.retract (F.monadLift ma : F m α) = ma := by
      unfold F.retract F.monadLift
      simp_all only [Monad.joinM, bind_pure, bind_map_left, id_eq]

    theorem map_id [Functor f] (x : F f α) : x.map id = x := by
      cases x; rfl

    theorem map_compose [Functor f] (g : α → β) (h : β → γ) (x : F f α) :
      x.map (h ∘ g) = (x.map g).map h := by
      cases x; rfl

    theorem runF_pure [Functor f] (a : α) (r : Type u) (kp : α → r) (kf : f r → r) :
      (F.pure a).runF kp kf = kp a := rfl

    theorem runF_bind [Functor f] (m : F f α) (f' : α → F f β) (r : Type u)
      (kp : β → r) (kf : f r → r) :
      (F.bind m f').runF kp kf = m.runF (fun a => (f' a).runF kp kf) kf := rfl

    theorem foldF_pure [Functor f] (pureF : α → r) (impureF : f r → r) (a : α) :
      F.foldF pureF impureF (F.pure a) = pureF a := rfl

end Properties

-- Example usage and properties
namespace Examples

  -- Example functor for testing
  inductive ConsoleF (α : Type u) : Type u where
    | getPutS : String → (String → α) → ConsoleF α
    | putStrLn : String → α → ConsoleF α

  instance : Functor ConsoleF where
    map f
      | ConsoleF.getPutS prompt k => ConsoleF.getPutS prompt (f ∘ k)
      | ConsoleF.putStrLn s next => ConsoleF.putStrLn s (f next)

  -- Helper functions
  def getLine (prompt : String) : F ConsoleF String :=
    F.monadLift (ConsoleF.getPutS prompt id)

  def putLine (s : String) : F ConsoleF Unit :=
    F.monadLift (ConsoleF.putStrLn s ())

  -- Example program
  def exampleProgram : F ConsoleF Unit := do
    let name ← getLine "What's your name? "
    putLine s!"Hello, {name}!"

  namespace ConsoleIO

    def interpreter : ConsoleF (IO α) → IO α
    | ConsoleF.getPutS prompt k => do
        IO.print prompt
        let input ← IO.getStdin >>= fun stdin => stdin.getLine
        k input.trim
    | ConsoleF.putStrLn s next => do
        IO.println s
        next

    def interpret : (F ConsoleF α) -> IO α := F.iterM interpreter

    #eval interpret exampleProgram

  end ConsoleIO

  namespace ConsoleStateM

    structure IOState where
      inputs  : List String   -- predetermined user input
      outputs : List String   -- accumulated output
    deriving Repr

    -- Pure interpreter into State IOState monad
    def interpreter : ConsoleF (StateM IOState α) → StateM IOState α
    | ConsoleF.getPutS _prompt k => do
        let s ← get
        match s.inputs with
        | input :: rest =>
          set { s with inputs := rest }
          k input
        | [] =>
          -- Fallback input if exhausted; you can customize this
          k "<no input>"

    | ConsoleF.putStrLn msg next => do
      let s ← get
      set { s with outputs := s.outputs ++ [msg] }
      next

    def interpret : F ConsoleF α -> StateM IOState α := F.iterM interpreter

    #guard
      let initial : IOState := { inputs := ["Alice"], outputs := [] }
      let (a, final) := interpret exampleProgram |>.run initial
      (a, final.outputs) = ((), ["Hello, Alice!"])

  end ConsoleStateM

end Examples
