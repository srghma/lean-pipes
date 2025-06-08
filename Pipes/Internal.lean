import Aesop
import Init.Control.State
import Batteries.Control.AlternativeMonad

-- Church-encoded Proxy type
@[inline] def Proxy (a' a b' b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1) :=
  ∀ {s : Type u},
    (r → s) →            -- Handle Pure
    (a' → (a → s) → s) → -- Handle Request
    (b → (b' → s) → s) → -- Handle Respond
    (m s → s) →          -- Handle M
    s

-- Basic constructors
@[inline] def Proxy.Pure (xr : r) : Proxy a' a b' b m r :=
  fun kp _ka _kb _km => kp xr

@[inline] def Proxy.Request (xa' : a') (k : a → Proxy a' a b' b m r) : Proxy a' a b' b m r :=
  fun kp ka kb km => ka xa' (fun a => k a kp ka kb km)

@[inline] def Proxy.Respond (xb : b) (k : b' → Proxy a' a b' b m r) : Proxy a' a b' b m r :=
  fun kp ka kb km => kb xb (fun b' => k b' kp ka kb km)

@[inline] def Proxy.M [Functor m] (mx : m r) : Proxy a' a b' b m r :=
  fun kp _ka _kb km => km (Functor.map kp mx)

-- Fold function (trivial for Church encoding)
@[inline] def foldProxy [Monad m]
  (ka : a' → (a → s) → s)
  (kb : b → (b' → s) → s)
  (km : (x : Type u) → (x → s) → m x → s)
  (kp : r → s)
  (p : Proxy a' a b' b m r) : s :=
  p kp ka kb (km _ id)

-- Bind operation
@[inline] def Proxy.bind [Monad m]
  (p0 : Proxy a' a b' b m c)
  (f : c → Proxy a' a b' b m d) :
  Proxy a' a b' b m d :=
  fun kp ka kb km =>
    p0 (fun c => f c kp ka kb km) ka kb km
@[inline] def Proxy.map [Monad m] (f : r → s) (p : Proxy a' a b' b m r) : Proxy a' a b' b m s :=
  Proxy.bind p (Proxy.Pure ∘ f)
@[inline] def Proxy.seq [Monad m] (pf : Proxy a' a b' b m (r → s)) (px : Unit → Proxy a' a b' b m r) : Proxy a' a b' b m s := Proxy.bind pf (fun f => Proxy.map f (px ()))
@[inline] def Proxy.request [Monad m] : a' -> Proxy a' a b' b m a := (Proxy.Request · Proxy.Pure)
@[inline] def Proxy.respond [Monad m] : b -> Proxy a' a b' b m b' := (Proxy.Respond · Proxy.Pure)
@[inline] def Proxy.monadLift [Functor m] : m x -> Proxy a' a b' b m x := Proxy.M

@[inline] instance [Monad m] : Functor (Proxy a' a b' b m) := { map := Proxy.map }
@[inline] instance [Monad m] : Pure (Proxy a' a b' b m) := ⟨Proxy.Pure⟩
@[inline] instance [Monad m] : Seq (Proxy a' a b' b m) := ⟨Proxy.seq⟩
@[inline] instance [Monad m] : Bind (Proxy a' a b' b m) := ⟨Proxy.bind⟩
@[inline] instance [Monad m] : Monad (Proxy a' a b' b m) where
@[inline] instance [Monad m] : MonadLift m (Proxy a' a b' b m) := ⟨Proxy.monadLift⟩

instance [Monad m] : LawfulMonad (Proxy a' a b' b m) := LawfulMonad.mk'
  (id_map := fun x => by rfl)
  (pure_bind := fun _ _ => by rfl)
  (bind_assoc := fun x _ _ => by rfl)

instance [Monad m] : LawfulApplicative (Proxy a' a b' b m) := inferInstance
instance [Monad m] : LawfulFunctor (Proxy a' a b' b m) := inferInstance

@[inline, simp]
def Proxy.failure [Alternative m] : Proxy a' a b' b m α :=
  fun _kp _ka _kb km => km Alternative.failure

-- From https://github.com/leanprover-community/mathlib4/blob/730e4db21155a3faee9cadd55d244dbf72f06391/Mathlib/Control/Combinators.lean#L14-L17
@[always_inline, inline, simp] def Monad.joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α := bind a id

@[inline, simp]
def Proxy.orElse [Monad m] [Alternative m]
  (x : Proxy a' a b' b m ret) (y : Unit → Proxy a' a b' b m ret) : Proxy a' a b' b m ret :=
  fun {result} kp _ka _kb km =>
    -- let mx : m result := x (fun a => pure (kp a)) (fun a' amres => let x := ka a'; ?a) (fun _ _ => Alternative.failure) Monad.joinM
    let mx : m result := x (fun a => pure (kp a)) (fun _ _ => Alternative.failure) (fun _ _ => Alternative.failure) Monad.joinM
    let my : Unit -> m result := fun _ => y () (fun a => pure (kp a)) (fun _ _ => Alternative.failure) (fun _ _ => Alternative.failure) Monad.joinM
    km (Alternative.orElse mx my)

@[inline] instance [Monad m] [Alternative m] : Alternative (Proxy a' a b' b m) := ⟨Proxy.failure, Proxy.orElse⟩
@[inline] instance [Monad m] [Alternative m] : AlternativeMonad (Proxy a' a b' b m) where

@[inline] instance [Functor m] [MonadState σ m] : MonadState σ (Proxy a' a b' b m) where
  get := Proxy.monadLift MonadState.get
  set s := Proxy.monadLift (MonadState.set s)
  modifyGet f := Proxy.monadLift (MonadState.modifyGet f)

@[inline] instance [Functor m] [MonadReader ρ m] : MonadReader ρ (Proxy a' a b' b m) where
  read := Proxy.monadLift MonadReader.read

instance [Monad m] [Alternative m] [LawfulAlternative m] [LawfulMonad m] : LawfulAlternative (Proxy a' a b' b m) where
  map_failure g := by rfl
  failure_seq x := by rfl
  map_orElse x y g := by rfl
  orElse_failure x := by
    sorry

  -- failure <|> y = y
  failure_orElse y := by
    sorry

  -- (x <|> y) <|> z = x <|> (y <|> z)
  orElse_assoc x y z := by
    sorry

-- Type aliases
abbrev Effect      := Proxy Empty Unit Unit Empty
abbrev Producer b  := Proxy Empty Unit Unit b
abbrev Pipe a b    := Proxy Unit a Unit b
abbrev Consumer a  := Proxy Unit a Unit Empty
abbrev Client a' a := Proxy a' a Unit Empty
abbrev Server b' b := Proxy Empty Unit b' b

abbrev Effect_        m r := forall {a' a b' b}, Proxy a'   a b'   b m r
abbrev Producer_ b    m r := forall {a' a},      Proxy a'   a Unit b m r
abbrev Consumer_ a    m r := forall {b' b},      Proxy Unit a b'   b m r
abbrev Server_   b' b m r := forall {a' a},      Proxy a'   a b'   b m r
abbrev Client_   a' a m r := forall {b' b},      Proxy a'   a b'   b m r

-- Kleisli composition for Proxy
def Proxy.kleisli_compose [Monad m]
  (f : b → Proxy a' a b' b m c)
  (g : a → Proxy a' a b' b m b) :
  a → Proxy a' a b' b m c :=
  fun a => Proxy.bind (g a) f

-- Run functions
@[always_inline, inline] def Proxy.runEffect [Monad m] (eff : Effect m r) : m r :=
  eff
    pure                                   -- Handle Pure
    (fun x _ => Empty.elim x)              -- Handle Request (impossible)
    (fun x _ => Empty.elim x)              -- Handle Respond (impossible)
    Monad.joinM                            -- Handle M

namespace AlternativeTest
  def testAlt1 : Proxy Empty Unit Unit Empty Option String := Proxy.failure
  def testAlt2 : Proxy Empty Unit Unit Empty Option String := Proxy.Pure $ "world"

  #guard Proxy.runEffect testAlt1 = .none
  #guard Proxy.runEffect testAlt2 = .some "world"

  #guard Proxy.runEffect (Proxy.orElse testAlt1 (fun _ => testAlt2)) = Proxy.runEffect testAlt2
  -- FIXME
  -- #guard Proxy.runEffect (testAlt1 <|> testAlt2) = Proxy.runEffect testAlt2
end AlternativeTest

-- Composition operations
@[inline] def Proxy.composeProxy [Monad m]
  (p0 :     Proxy x' x b' b m a')
  (fb : b → Proxy x' x c' c m b') :
            Proxy x' x c' c m a' :=
  fun kp ka kb km =>
    p0 kp ka
      (fun b k => fb b (fun b' => k b') ka kb km)
      km

@[inline] def Proxy.composeProxyFlipped [Monad m]
    (fb : b → Proxy x' x c' c m b')
    (p0 :     Proxy x' x b' b m a') :
              Proxy x' x c' c m a' := Proxy.composeProxy p0 fb

infixl:60 " >c> " => Proxy.composeProxy
infixl:60 " <c< " => Proxy.composeProxyFlipped

partial def Proxy.connectProducerConsumer [Monad m]
  (producer : Producer b m r)
  (consumer : Consumer b m r) :
  Effect m r := fun {result} kp _ka _kc km =>
    producer
      (fun r => consumer (fun r' => kp r') (fun () f => f ()) (fun _ _ => Empty.elim) km)
      (fun v _ => Empty.elim v)
      (fun b k => k () (fun () => connectProducerConsumer (k ()) consumer kp _ka _kc km))
      km

-- The correct composition operator for connecting Producer to Consumer
partial def Proxy.connectProducerConsumer [Monad m]
  (producer : Producer b m r)
  (consumer : Consumer b m r) :
  Effect m r := fun {result} kp _ka _kc km =>
    producer
      kp
      (fun empty _ => Empty.elim empty)
      (fun xb cont_prod =>
        consumer
          kp
          (fun _ cont_cons =>
            let new_producer : Producer b m r := ?a
            let new_consumer : Consumer b m r := fun newkpure newkreq newkresp newkm => newkreq () fun newb => cont_cons newb
            Proxy.connectProducerConsumer new_producer new_consumer kp _ka _kc km)
          (fun empty _ => Empty.elim empty)
          km)
      km

infixl:60 " >-> " => Proxy.connectProducerConsumer
infixl:60 " <-< " => fun consumer producer => Proxy.connectProducerConsumer producer consumer

-- Additional utility functions
def Proxy.yield [Monad m] : b -> Producer b m Unit := respond

def Proxy.await [Monad m] : Consumer a m a := request ()

partial def Proxy.cat [Monad m] [Inhabited r] : Pipe a a m r :=
  fun kp ka kb km => ka () (fun a => kb a (fun _ => cat kp ka kb km))

-- Pipe composition (left-to-right)
def Proxy.pipeCompose [Monad m]
  (p1 : Proxy a' a b' b m r)
  (p2 : Proxy b' b c' c m r) :
  Proxy a' a c' c m r :=
  fun kp ka kb km =>
    p1 kp ka
      (fun _b k => p2 kp (fun b' _f => k b') kb km)
      km

def Proxy.forM [Monad m] (xs : List a) (f : a → Proxy x' x b' b m Unit) : Proxy x' x b' b m Unit :=
  List.foldl (fun acc x kpure kreq kresp km =>
    acc (fun _ => f x kpure kreq kresp km) kreq kresp km) (Proxy.Pure ()) xs

def Proxy.List.each [Monad m] [Functor m] : List a → Producer_ a m Unit
| []      => Proxy.Pure ()
| (a::as) => Proxy.Respond a (fun _ => Proxy.List.each as)

def Proxy.Array.each [Monad m] [Functor m] : (Array a) -> Producer_ a m Unit := (Proxy.List.each ·.toList)

namespace Examples

def numbers : Nat -> Producer Nat m Unit
  | 0 => Proxy.Pure ()
  | n+1 => Proxy.Respond n (fun () => numbers n)

-- partial def printer : Consumer Nat IO Unit :=
--   Proxy.Request () (fun n =>
--     Proxy.bind (Proxy.M (IO.println s!"Number: {n}")) (fun _ =>
--     printer))

partial def consume : Consumer Nat (StateM (List Nat)) Unit :=
  Proxy.Request () (fun n =>
    Proxy.bind (Proxy.M (modify (fun s => s ++ [n]))) (fun _ =>
    consume))

-- Example pipeline
def examplePipeline : Effect (StateM (List Nat)) Unit := numbers 5 >-> consume

def exampleIO : List Nat := ((Proxy.runEffect examplePipeline).run []).run.2

#guard exampleIO = [1, 2, 3, 4, 5]

end Examples
