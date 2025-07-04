import Aesop
import Pipes.Internal
import Canonical
import Mathlib.Data.Nat.Init

namespace Proxy

-- The key insight: we need to encode the mutual recursion as a single relation
inductive PullPushWF (a' a b' b c' c m r) where
  | pullR_go : (b → Proxy b' b c' c m r) → Proxy a' a b' b m r → PullPushWF a' a b' b c' c m r
  | pushL_reg : (b' → Proxy a' a b' b m r) → Proxy b' b c' c m r → PullPushWF a' a b' b c' c m r

inductive PullPushWFRel :
    PullPushWF a' a b' b c' c m r → PullPushWF a' a b' b c' c m r → Prop where
  -- pullR transitions
  | pullR_request : PullPushWFRel (.pullR_go fb (fa a)) (.pullR_go fb (.Request a' fa))
  | pullR_respond : PullPushWFRel (.pushL_reg fb' (fb b)) (.pullR_go fb (.Respond b fb'))
  | pullR_m : PullPushWFRel (.pullR_go fb (cont x)) (.pullR_go fb (.M m cont))
  -- pushL transitions
  | pushL_request : PullPushWFRel (.pullR_go fb (fb' b')) (.pushL_reg fb' (.Request b' fb))
  | pushL_respond : PullPushWFRel (.pushL_reg fb' (fc' c')) (.pushL_reg fb' (.Respond c fc'))
  | pushL_m : PullPushWFRel (.pushL_reg fb' (cont x)) (.pushL_reg fb' (.M m cont))

instance : WellFoundedRelation (PullPushWF a' a b' b c' c m r) where
  rel := PullPushWFRel
  wf := by
    constructor
    intro p
    -- The key insight: prove both accessibility results simultaneously
    -- using a single induction that handles both cases
    suffices h : (∀ (fb : b → Proxy b' b c' c m r) (proxy : Proxy a' a b' b m r),
        Acc PullPushWFRel (.pullR_go fb proxy)) ∧
        (∀ (fb' : b' → Proxy a' a b' b m r) (q : Proxy b' b c' c m r),
        Acc PullPushWFRel (.pushL_reg fb' q)) by
      cases p with
      | pullR_go fb proxy => exact h.1 fb proxy
      | pushL_reg fb' q => exact h.2 fb' q

    -- Now prove both simultaneously using mutual strong induction
    constructor
    · -- pullR_acc
      intro fb proxy
      induction proxy generalizing fb with
      | Request a' fa ih =>
        apply Acc.intro
        intro y h
        cases h with
        | pullR_request => exact ih _ _
      | Respond xb fb' ih2 =>
        apply Acc.intro
        intro y h
        cases h with
        | pullR_respond =>
          apply Acc.intro
          intro w h2
          induction fb xb generalizing fb' with
          | Request xb'3 fb3 ih3 =>
            exact ih3 xb fb' (fun a_1 fb_1 => ih2 a_1 fb_1) h2
          | Respond c3 fc'3 ih3 =>
            exact ih3 sorry fb' (fun a_1 fb_1 => ih2 a_1 fb_1) h2
          | M m3 cont3 ih3 =>
            exact ih3 sorry fb' (fun a_1 fb_1 => ih2 a_1 fb_1) h2
          | Pure r3 =>
            apply Acc.intro
            intro y3 h3
            cases h3 with
            | pullR_request => sorry
            | pullR_respond => sorry
            | pullR_m => sorry
            | pushL_request => sorry
            | pushL_respond => sorry
            | pushL_m => sorry
      | M m cont ih =>
        apply Acc.intro
        intro y h
        cases h with
        | pullR_m => exact ih _ _
      | Pure r =>
        apply Acc.intro
        intro y h
        cases h
    · -- pushL_acc
      intro fb' q
      induction q generalizing fb' with
      | Request b' fb ih =>
        apply Acc.intro
        intro y h
        cases h with
        | pushL_request =>
          -- This transitions to pullR_go, use the first part
          apply Acc.intro
          intro w h2
          aesop?
      | Respond c fc' ih =>
        apply Acc.intro
        intro y h
        cases h with
        | pushL_respond => exact ih _ _
      | M m cont ih =>
        apply Acc.intro
        intro y h
        cases h with
        | pushL_m => exact ih _ _
      | Pure r =>
        apply Acc.intro
        intro y h
        aesop?

-- Now define the functions with proper termination
mutual
def pullR (p : Proxy a' a b' b m r) (fb : b → Proxy b' b c' c m r) : Proxy a' a c' c m r :=
  match p with
  | Request a' fa  => Request a' (fun a => pullR (fa a) fb)
  | Respond b  fb' => pushL fb' (fb b)
  | M m cont       => M m (fun x => pullR (cont x) fb)
  | Pure r         => Pure r
  -- termination_by structural PullPushWF.pullR_go fb p
  termination_by PullPushWF.pullR_go fb p
  decreasing_by all_goals constructor

def pushL (fb' : b' → Proxy a' a b' b m r) (p : Proxy b' b c' c m r) : Proxy a' a c' c m r :=
  match p with
  | Request b' fb  => pullR (fb' b') fb
  | Respond c  fc' => Respond c (fun c' => pushL fb' (fc' c'))
  | M m cont       => M m (fun x => pushL fb' (cont x))
  | Pure r         => Pure r
  /- termination_by structural PullPushWF.pushL_reg fb' p -/
  termination_by PullPushWF.pushL_reg fb' p
  decreasing_by all_goals constructor
end

notation p ">>~" fb => pullR p fb
notation fb' "+>>" p => pushL fb' p

end Proxy
