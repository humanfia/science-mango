import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineRestrictedParentTransportV2

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveRestrictedCoarseKatzTaoV1

noncomputable section

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The parent map of the fully restricted cover is the original parent map
after undoing the active-coarse `Fin` reindexing. -/
theorem restrictedCoarseEquivActive_parent
    (S : StickyScaleCover fine rho) (i : {i // i ∈ S.activeFine}) :
    restrictedCoarseEquivActive S
        ((activeFineRestrictedScaleCover S).parent i) =
      ⟨S.parent i.1, S.parent_mem i.1 i.2⟩ := by
  unfold restrictedCoarseEquivActive activeFineRestrictedScaleCover
  exact S.activeCoarse.equivFin.symm_apply_apply
    ⟨S.parent i.1, S.parent_mem i.1 i.2⟩

#print axioms restrictedCoarseEquivActive_parent

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineRestrictedParentTransportV2
