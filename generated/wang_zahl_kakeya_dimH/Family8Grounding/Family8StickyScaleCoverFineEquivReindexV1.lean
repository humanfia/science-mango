import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

/-!
# Fine-index equivalence reindexing of a sticky scale cover

The coarse cover and parent geometry are retained literally.  This is a
pure finite reindexing constructor used by the q-fresh readiness transport.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8StickyScaleCoverFineEquivReindexV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace StickyScaleCover

variable {delta rho : NNReal} {sourceIndex targetIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  [Fintype targetIndex] [DecidableEq targetIndex]
  {source : UniformTubeFamily delta sourceIndex}

/-- Reindex an all-active fine family along an exact tube equivalence while
leaving every coarse field literal. -/
noncomputable def reindexFineOfActiveUniv
    (S : StickyScaleCover source rho)
    (target : UniformTubeFamily delta targetIndex)
    (e : targetIndex ≃ sourceIndex)
    (htube : ∀ i, target.tubes i = source.tubes (e i))
    (hsourceActive : S.activeFine = Finset.univ)
    (htargetRefined : target.refinement.refined = Finset.univ) :
    StickyScaleCover target rho := by
  classical
  exact
    { coarseCard := S.coarseCard
      coarse := S.coarse
      activeFine := Finset.univ
      activeCoarse := S.activeCoarse
      parent := fun i => S.parent (e i)
      activeFine_eq_refined := htargetRefined.symm
      activeCoarse_eq_refined := S.activeCoarse_eq_refined
      parent_mem := by
        intro i _hi
        apply S.parent_mem (e i)
        rw [hsourceActive]
        exact Finset.mem_univ _
      parent_surjective := by
        intro k hk
        obtain ⟨i, _hi, hparent⟩ := S.parent_surjective k hk
        refine ⟨e.symm i, Finset.mem_univ _, ?_⟩
        rw [e.apply_symm_apply]
        exact hparent
      carrier_subset := by
        intro i _hi
        rw [htube i]
        apply S.carrier_subset (e i)
        rw [hsourceActive]
        exact Finset.mem_univ _ }

@[simp] theorem reindexFineOfActiveUniv_coarse
    (S : StickyScaleCover source rho)
    (target : UniformTubeFamily delta targetIndex)
    (e : targetIndex ≃ sourceIndex)
    (htube : ∀ i, target.tubes i = source.tubes (e i))
    (hsourceActive : S.activeFine = Finset.univ)
    (htargetRefined : target.refinement.refined = Finset.univ) :
    (reindexFineOfActiveUniv S target e htube hsourceActive
      htargetRefined).coarse = S.coarse := rfl

@[simp] theorem reindexFineOfActiveUniv_activeCoarse
    (S : StickyScaleCover source rho)
    (target : UniformTubeFamily delta targetIndex)
    (e : targetIndex ≃ sourceIndex)
    (htube : ∀ i, target.tubes i = source.tubes (e i))
    (hsourceActive : S.activeFine = Finset.univ)
    (htargetRefined : target.refinement.refined = Finset.univ) :
    (reindexFineOfActiveUniv S target e htube hsourceActive
      htargetRefined).activeCoarse = S.activeCoarse := rfl

/-- A parent fibre is unchanged up to the same fine-index equivalence. -/
noncomputable def reindexFineOfActiveUnivFiberEquiv
    (S : StickyScaleCover source rho)
    (target : UniformTubeFamily delta targetIndex)
    (e : targetIndex ≃ sourceIndex)
    (htube : ∀ i, target.tubes i = source.tubes (e i))
    (hsourceActive : S.activeFine = Finset.univ)
    (htargetRefined : target.refinement.refined = Finset.univ)
    (k : Fin S.coarseCard) :
    {i // i ∈
      (reindexFineOfActiveUniv S target e htube hsourceActive
        htargetRefined).fiber k} ≃
      {j // j ∈ S.fiber k} := by
  classical
  let T := reindexFineOfActiveUniv S target e htube hsourceActive
    htargetRefined
  refine
    { toFun := fun i => ⟨e i.1, ?_⟩
      invFun := fun j => ⟨e.symm j.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hi := (T.mem_fiber i.1 k).mp i.2
    apply (S.mem_fiber (e i.1) k).mpr
    refine ⟨?_, hi.2⟩
    rw [hsourceActive]
    exact Finset.mem_univ _
  · have hj := (S.mem_fiber j.1 k).mp j.2
    apply (T.mem_fiber (e.symm j.1) k).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change S.parent (e (e.symm j.1)) = k
    rw [e.apply_symm_apply]
    exact hj.2
  · intro i
    apply Subtype.ext
    exact e.symm_apply_apply i.1
  · intro j
    apply Subtype.ext
    exact e.apply_symm_apply j.1

theorem reindexFineOfActiveUniv_fiber_card_eq
    (S : StickyScaleCover source rho)
    (target : UniformTubeFamily delta targetIndex)
    (e : targetIndex ≃ sourceIndex)
    (htube : ∀ i, target.tubes i = source.tubes (e i))
    (hsourceActive : S.activeFine = Finset.univ)
    (htargetRefined : target.refinement.refined = Finset.univ)
    (k : Fin S.coarseCard) :
    ((reindexFineOfActiveUniv S target e htube hsourceActive
      htargetRefined).fiber k).card = (S.fiber k).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr
    (reindexFineOfActiveUnivFiberEquiv S target e htube hsourceActive
      htargetRefined k)

#print axioms reindexFineOfActiveUniv
#print axioms reindexFineOfActiveUniv_coarse
#print axioms reindexFineOfActiveUniv_activeCoarse
#print axioms reindexFineOfActiveUnivFiberEquiv
#print axioms reindexFineOfActiveUniv_fiber_card_eq

end StickyScaleCover
end
end Family8StickyScaleCoverFineEquivReindexV1
