abbrev CProxy (a' a b' b : Type u) (m : Type u → Type u) (r : Type u) : Type (u+1) :=
  ∀ (s : Type u),
    (a' → (a → s) → s) →       -- Handle Request
    (b → (b' → s) → s) →       -- Handle Respond
    (∀ x, (x → s) → m x → s) → -- Handle
    (r → s) →                  -- Handle Pure
    s

namespace CProxy

-- Basic constructors
abbrev Pure (xr : r) : CProxy a' a b' b m r :=
  fun _s _ka _kb _km kp => kp xr

abbrev Request (xa' : a') (k : a → CProxy a' a b' b m r) : CProxy a' a b' b m r :=
  fun s ka kb km kp => ka xa' (fun xa => k xa s ka kb km kp)

abbrev Respond (xb : b) (k : b' → CProxy a' a b' b m r) : CProxy a' a b' b m r :=
  fun s ka kb km kp => kb xb (fun b' => k b' s ka kb km kp)

abbrev M (mx : m r) : CProxy a' a b' b m r :=
  fun _s _ka _kb km kp => km r kp mx

-- Fold function (trivial for Church encoding)
abbrev foldProxy
  (ka : a' → (a → s) → s)
  (kb : b → (b' → s) → s)
  (km : (x : Type u) → (x → s) → m x → s)
  (kp : r → s)
  (p : CProxy a' a b' b m r) : s :=
  p s ka kb km kp

-- Bind operation
abbrev bind
  (p0 : CProxy a' a b' b m c)
  (f : c → CProxy a' a b' b m d) :
  CProxy a' a b' b m d :=
  fun s ka kb km kp =>
    p0 s ka kb km (fun c => f c s ka kb km kp)

abbrev map (f : r → s) (p : CProxy a' a b' b m r) : CProxy a' a b' b m s := bind p (Pure ∘ f)
abbrev seq (pf : CProxy a' a b' b m (r → s)) (px : PUnit → CProxy a' a b' b m r) : CProxy a' a b' b m s := bind pf (map · (px ()))

end CProxy

instance : Functor (CProxy a' a b' b m) := { map := CProxy.map }
instance : Pure (CProxy a' a b' b m) := ⟨CProxy.Pure⟩
instance : Seq (CProxy a' a b' b m) := ⟨CProxy.seq⟩
instance : Bind (CProxy a' a b' b m) := ⟨CProxy.bind⟩
instance : Monad (CProxy a' a b' b m) where
instance : MonadLift m (CProxy a' a b' b m) := ⟨CProxy.M⟩


instance [MonadState σ m] : MonadState σ (CProxy a' a b' b m) where
  get := CProxy.M MonadState.get
  set s := CProxy.M (MonadState.set s)
  modifyGet f := CProxy.M (MonadState.modifyGet f)

instance [MonadReader ρ m] : MonadReader ρ (CProxy a' a b' b m) where
  read := CProxy.M MonadReader.read

-------------------------------------------

instance : LawfulMonad (CProxy a' a b' b m) := LawfulMonad.mk'
  (id_map := fun x => by rfl)
  (pure_bind := fun _ _ => by rfl)
  (bind_assoc := fun x _ _ => by rfl)

instance : LawfulApplicative (CProxy a' a b' b m) := inferInstance
instance : LawfulFunctor (CProxy a' a b' b m) := inferInstance
