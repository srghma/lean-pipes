import Aesop
-- import Mathlib.CategoryTheory.Category.Basic
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
    refine ⟨fun p => ?_⟩

    -- The key: define both H1 and H2 mutually, similar to your working example
    have H1 (fb : b → Proxy b' b c' c m r) (proxy : Proxy a' a b' b m r)
        (h_pushL : ∀ (fb' : b' → Proxy a' a b' b m r) (q : Proxy b' b c' c m r),
                   Acc PullPushWFRel (.pushL_reg fb' q)) :
        Acc PullPushWFRel (.pullR_go fb proxy) := by
      induction proxy with
      | Request a' fa ih =>
        exact ⟨_, fun | _, .pullR_request => ih _⟩
      | Respond b fb' =>
        exact ⟨_, fun | _, .pullR_respond => h_pushL fb' (fb b)⟩
      | M m cont ih =>
        exact ⟨_, fun | _, .pullR_m => ih _⟩
      | Pure r =>
        exact ⟨_, nofun⟩

    have H2 (fb' : b' → Proxy a' a b' b m r) (q : Proxy b' b c' c m r) :
        Acc PullPushWFRel (.pushL_reg fb' q) := by
      induction q with
      | Request xb' xfb xih =>
        exact ⟨_, fun | _, .pushL_request => H1 xfb (fb' xb') (fun x1 x2 => sorry)⟩
      | Respond c fc' ih =>
        exact ⟨_, fun | _, .pushL_respond => ih _⟩
      | M m cont ih =>
        exact ⟨_, fun | _, .pushL_m => ih _⟩
      | Pure r =>
        exact ⟨_, nofun⟩

    cases p with
    | pullR_go fb proxy => exact H1 fb proxy (fun _ _ => H2 _ _)
    | pushL_reg fb' q => exact H2 fb' q

-- Now define the functions with proper termination
mutual
def pullR [Inhabited r] (p : Proxy a' a b' b m r) (fb : b → Proxy b' b c' c m r) : Proxy a' a c' c m r :=
  match p with
  | Request a' fa  => Request a' (fun a => pullR (fa a) fb)
  | Respond b  fb' => pushL fb' (fb b)
  | M m cont       => M m (fun x => pullR (cont x) fb)
  | Pure r         => Pure r
  termination_by PullPushWF.pullR_go fb p
  decreasing_by all_goals constructor

def pushL [Inhabited r] (fb' : b' → Proxy a' a b' b m r) (p : Proxy b' b c' c m r) : Proxy a' a c' c m r :=
  match p with
  | Request b' fb  => pullR (fb' b') fb
  | Respond c  fc' => Respond c (fun c' => pushL fb' (fc' c'))
  | M m cont       => M m (fun x => pushL fb' (cont x))
  | Pure r         => Pure r
  termination_by PullPushWF.pushL_reg fb' p
  decreasing_by all_goals constructor
end

notation p ">>~" fb => pullR p fb
notation fb' "+>>" p => pushL fb' p

end Proxy
