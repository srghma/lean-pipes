import Aesop
import Init.Control.State
import Batteries.Control.AlternativeMonad

-- Church-encoded Proxy type
@[inline] def Proxy (a' a b' b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1) :=
  ∀ {result : Type u},
    (r → result) →                 -- Handle Pure
    (a' → (a → result) → result) → -- Handle Request
    (b → (b' → result) → result) → -- Handle Respond
    (m result → result) →          -- Handle M
    result

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

-- Type aliases
abbrev Effect      := Proxy Empty Unit Unit Empty
abbrev Producer b  := Proxy Empty Unit Unit b
abbrev Pipe a b    := Proxy Unit a Unit b
abbrev Consumer a  := Proxy Unit a Unit Empty
abbrev Client a' a := Proxy a' a Unit Empty
abbrev Server b' b := Proxy Empty Unit b' b

-- Kleisli composition for Proxy
def Proxy.kleisli_compose [Monad m]
  (f : b → Proxy a' a b' b m c)
  (g : a → Proxy a' a b' b m b) :
  a → Proxy a' a b' b m c :=
  fun a => Proxy.bind (g a) f

-- From https://github.com/leanprover-community/mathlib4/blob/730e4db21155a3faee9cadd55d244dbf72f06391/Mathlib/Control/Combinators.lean#L14-L17
@[always_inline, inline, simp] def Monad.joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α := bind a id

-- Run functions
@[always_inline, inline] def Proxy.runEffect [Monad m] (eff : Effect m r) : m r :=
  eff
    pure                                   -- Handle Pure
    (fun x _ => Empty.elim x)              -- Handle Request (impossible)
    (fun x _ => Empty.elim x)              -- Handle Respond (impossible)
    Monad.joinM                            -- Handle M

-- Composition operations
def Proxy.composeResponse [Monad m]
  (p0 : Proxy x' x b' b m a')
  (fb : b → Proxy x' x c' c m b') :
  Proxy x' x c' c m a' :=
  fun kp ka kb km =>
    p0 kp ka
      (fun b k => fb b (fun b' => k b') ka kb km)
      km

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
