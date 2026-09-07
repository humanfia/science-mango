import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineSameCoarseCoverV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover

noncomputable section

/-!
# Active-fine reindexing with the same coarse family

Only the fine index acquires its active-membership proof.  The coarse family,
coarse index type, active coarse set, and parent map remain literal.
-/

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

noncomputable def activeFineSameCoarseCover
    (S : StickyScaleCover fine rho) :
    StickyScaleCover (activeFineRestrictedFamily S) rho :=
  { coarseCard := S.coarseCard
    coarse := S.coarse
    activeFine := Finset.univ
    activeCoarse := S.activeCoarse
    parent := fun i => S.parent i.1
    activeFine_eq_refined := rfl
    activeCoarse_eq_refined := S.activeCoarse_eq_refined
    parent_mem := by
      intro i _hi
      exact S.parent_mem i.1 i.2
    parent_surjective := by
      intro k hk
      obtain ⟨i, hi, hparent⟩ := S.parent_surjective k hk
      exact ⟨⟨i, hi⟩, Finset.mem_univ _, hparent⟩
    carrier_subset := by
      intro i _hi
      exact S.carrier_subset i.1 i.2 }

@[simp]
theorem activeFineSameCoarseCover_activeFine
    (S : StickyScaleCover fine rho) :
    (activeFineSameCoarseCover S).activeFine = Finset.univ :=
  rfl

@[simp]
theorem activeFineSameCoarseCover_activeCoarse
    (S : StickyScaleCover fine rho) :
    (activeFineSameCoarseCover S).activeCoarse = S.activeCoarse :=
  rfl

#print axioms activeFineSameCoarseCover
#print axioms activeFineSameCoarseCover_activeFine
#print axioms activeFineSameCoarseCover_activeCoarse

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineSameCoarseCoverV1
