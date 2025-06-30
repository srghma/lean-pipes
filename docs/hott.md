https://perfect-math-class.leni.sh/lecture/conclusion/

inductive IntBase where
  | pos : Nat → IntBase
  | neg : Nat → IntBase
deriving Repr, DecidableEq

def IntRel : IntBase → IntBase → Prop
  | IntBase.pos 0, IntBase.neg 0 => True
  | IntBase.neg 0, IntBase.pos 0 => True
  | a, b                         => a = b

def Int : Type := Quot IntRel

def succBase : IntBase → IntBase
  | IntBase.pos n     => IntBase.pos (n + 1)
  | IntBase.neg 0     => IntBase.pos 1
  | IntBase.neg (n+1) => IntBase.neg n

theorem succ_respects_rel :
  ∀ a b : IntBase, IntRel a b → Quot.mk IntRel (succBase a) = Quot.mk IntRel (succBase b) := by
  intro a b h
  cases a with
  | pos n =>
    cases b with
    | pos m =>
      cases n with
      | zero =>
        cases m with
        | zero => rfl
        | succ m' =>
          simp [IntRel] at h
      | succ n' =>
        cases m with
        | zero =>
          simp [IntRel] at h
        | succ m' =>
          simp [IntRel] at h
          rw [h]
    | neg m =>
      cases n with
      | zero =>
        cases m with
        | zero =>
          -- This is the special case: pos 0 ~ neg 0
          rfl
        | succ m' =>
          simp [IntRel] at h
      | succ n' =>
        simp [IntRel] at h
  | neg n =>
    cases b with
    | pos m =>
      cases n with
      | zero =>
        cases m with
        | zero =>
          -- This is the special case: neg 0 ~ pos 0
          rfl
        | succ m' =>
          simp [IntRel] at h
      | succ n' =>
        simp [IntRel] at h
    | neg m =>
      cases n with
      | zero =>
        cases m with
        | zero => rfl
        | succ m' =>
          simp [IntRel] at h
      | succ n' =>
        cases m with
        | zero =>
          simp [IntRel] at h
        | succ m' =>
          simp [IntRel] at h
          rw [h]

def succ : Int → Int :=
  Quot.lift (fun x => Quot.mk IntRel (succBase x)) succ_respects_rel
