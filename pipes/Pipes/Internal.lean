module
public section
/-
- a' is the type of values flowing upstream (input)
- a  is the type of values flowing downstream (input)
- b' is the type of values flowing upstream (output)
- b  is the type of values flowing downstream (output)
- m  is the base monad
- r  is the return type
-/

/-
inductive Proxy.{u, v, w}
  (a' : Type u) (a : Type u)
  (b' : Type v) (b : Type v)
  (m : Type w → Type w)
  (r : Type w) : Type (max (max (u+1) (v+1)) (w+1))
  where
  | Request : a' → (a → Proxy a' a b' b m r) → Proxy a' a b' b m r
  | Respond : b → (b' → Proxy a' a b' b m r) → Proxy a' a b' b m r
  | M       {x : Type w} (op : m x) (cont : x → Proxy a' a b' b m r) : Proxy a' a b' b m r
  | Pure    : r → Proxy a' a b' b m r

inductive Proxy.{ua', ua, ub', ub, umi, umo, ur}
  (a' : Type ua') (a : Type ua)
  (b' : Type ub') (b : Type ub)
  (m : Type umi → Type umo)
  (r : Type ur)
  where
  | Request : a' → (a → Proxy a' a b' b m r) → Proxy a' a b' b m r
  | Respond : b → (b' → Proxy a' a b' b m r) → Proxy a' a b' b m r
  | M       {x : Type umi} (op : m x) (cont : x → Proxy a' a b' b m r) : Proxy a' a b' b m r
  | Pure    : r → Proxy a' a b' b m r
-/

-- inductive ProxyImpl.{u} (x : Type u) (a' a b' b : Type u) (m : Type u → Type u) (r : Type u) : Type u
--   | I_Request : a' → (a → ProxyImpl x a' a b' b m r) → ProxyImpl x a' a b' b m r
--   | I_Respond : b → (b' → ProxyImpl x a' a b' b m r) → ProxyImpl x a' a b' b m r
--   | I_M       (op : m x) (cont : x → ProxyImpl x a' a b' b m r) : ProxyImpl x a' a b' b m r
--   | I_Pure    : r → ProxyImpl x a' a b' b m r

inductive Proxy.{u} (a' a b' b : Type u) (m : Type u → Type u) (r : Type u) : Type (u + 1)
  | Request : a' → (a → Proxy a' a b' b m r) → Proxy a' a b' b m r
  | Respond : b → (b' → Proxy a' a b' b m r) → Proxy a' a b' b m r
  | M       {x : Type u} (op : m x) (cont : x → Proxy a' a b' b m r) : Proxy a' a b' b m r
  | Pure    : r → Proxy a' a b' b m r

instance [Inhabited r] : Inhabited (Proxy a' a b' b m r) where
  default := .Pure default

--- instance [BEq a'] [BEq a] [BEq b] [BEq b'] [BEq r] : BEq (Proxy a' a b' b Id r) where
---   beq
---     | .Pure r₁, .Pure r₂ => r₁ == r₂
---     | .Request a₁ _, .Request a₂ _ => a₁ == a₂
---     | .Respond b₁ _, .Respond b₂ _ => b₁ == b₂
---     | .M op₁ _, .M op₂ _ => op₁ == op₂
---     | _, _ => false

-- instance
--   {a' a b' b r : Type u} {m : Type u → Type u}
--   [DecidableEq a'] [DecidableEq b] [DecidableEq r] [DecidableEq (m PUnit)] :
--   DecidableEq (Proxy a' a b' b m r) where
--   decEq
--     | .Pure r₁, .Pure r₂ =>
--         match decEq r₁ r₂ with
--         | isTrue h => isTrue (by rw [h])
--         | isFalse h => isFalse (by intro h'; injection h' with h₁; exact h h₁)
--     | .Request a₁ _, .Request a₂ _ =>
--         match decEq a₁ a₂ with
--         | isTrue h => isTrue (by rw [h])
--         | isFalse h => isFalse (by intro h'; injection h' with h₁ _; exact h h₁)
--     | .Respond b₁ _, .Respond b₂ _ =>
--         match decEq b₁ b₂ with
--         | isTrue h => isTrue (by rw [h])
--         | isFalse h => isFalse (by intro h'; injection h' with h₁ _; exact h h₁)
--     | .M op₁ _, .M op₂ _ =>
--         match decEq op₁ op₂ with
--         | isTrue h => isTrue (by rw [h])
--         | isFalse h => isFalse (by intro h'; injection h' with h₁ _; exact h h₁)
--     | _, _ => isFalse (by intro h; cases h)

namespace Proxy

def foldProxy
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

end Proxy

-- This is equivalent to [foldProxy Request Respond (fun _ => M)], but using
-- that definition makes some proofs harder.
-- NOTE: in coq diff order of args
@[inline, simp, specialize] def Proxy.bind
  (p0 : Proxy a' a b' b m c)
  (f : c → Proxy a' a b' b m d) :
  Proxy a' a b' b m d :=
  match p0 with
  | .Request xa' k => .Request xa' (fun a => bind (k a) f)
  | .Respond xb k => .Respond xb (fun b' => bind (k b') f)
  | .M mx k => .M mx (fun x => bind (k x) f)
  | .Pure xc => f xc

@[inline, specialize] abbrev Proxy.map (f : r → s) (p : Proxy a' a b' b m r) : Proxy a' a b' b m s :=
  bind p (fun val => Proxy.Pure (f val))

@[inline, specialize] abbrev Proxy.seq (pf : Proxy a' a b' b m (r → s)) (px : PUnit → Proxy a' a b' b m r) : Proxy a' a b' b m s :=
  bind pf (map · (px ()))

@[inline, specialize] abbrev Proxy.monadLift (mx : m r) : Proxy a' a b' b m r := Proxy.M mx Proxy.Pure

instance : Functor (Proxy a' a b' b m) := { map := Proxy.map }
instance : Pure (Proxy a' a b' b m) := ⟨Proxy.Pure⟩
instance : Seq (Proxy a' a b' b m) := ⟨Proxy.seq⟩
instance : Bind (Proxy a' a b' b m) := ⟨Proxy.bind⟩
instance : Monad (Proxy a' a b' b m) where
instance : MonadLift m (Proxy a' a b' b m) := ⟨Proxy.monadLift⟩

instance [MonadState σ m] : MonadState σ (Proxy a' a b' b m) where
  get := Proxy.monadLift MonadState.get
  set := Proxy.monadLift ∘ MonadState.set
  modifyGet := Proxy.monadLift ∘ MonadState.modifyGet

instance [MonadReader ρ m] : MonadReader ρ (Proxy a' a b' b m) where
  read := Proxy.monadLift MonadReader.read

-------------------------------------------

instance : LawfulMonad (Proxy a' a b' b m) := LawfulMonad.mk'
  (id_map := by
    intro α x
    induction x with
    | Request a' k ih => simp [Functor.map]; funext a; exact ih a
    | Respond b k ih => simp [Functor.map]; funext b'; exact ih b'
    | M mx k ih => simp [Functor.map]; funext x; exact ih x
    | Pure r => rfl
  )
  (pure_bind := by intro α β x f; rfl)
  (bind_assoc := by
    intro α β γ x f g
    induction x with
    | Request a' k ih => simp [Bind.bind]; funext a; exact ih a;
    | Respond b k ih => simp [Bind.bind]; funext b'; exact ih b';
    | M mx k ih => simp [Bind.bind]; funext x; exact ih x;
    | Pure r => rfl
  )

instance : LawfulApplicative (Proxy a' a b' b m) := inferInstance
instance : LawfulFunctor (Proxy a' a b' b m) := inferInstance

-- Type aliases
abbrev Effect      := Proxy PEmpty PUnit PUnit PEmpty
abbrev Producer b  := Proxy PEmpty PUnit PUnit b
abbrev Pipe a b    := Proxy PUnit a PUnit b -- downstream input -> downstream output
abbrev Consumer a  := Proxy PUnit a PUnit PEmpty
abbrev Client a' a := Proxy a' a PUnit PEmpty
abbrev Server b' b := Proxy PEmpty PUnit b' b

abbrev Effect_        m r := forall {a' a b' b}, Proxy a'   a b'   b m r
abbrev Producer_ b    m r := forall {a' a},      Proxy a'   a PUnit b m r
abbrev Consumer_ a    m r := forall {b' b},      Proxy PUnit a b'   b m r
abbrev Server_   b' b m r := forall {a' a},      Proxy a'   a b'   b m r
abbrev Client_   a' a m r := forall {b' b},      Proxy a'   a b'   b m r
