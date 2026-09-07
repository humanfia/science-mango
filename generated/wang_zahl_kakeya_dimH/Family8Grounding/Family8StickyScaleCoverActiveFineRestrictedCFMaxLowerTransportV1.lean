import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedCFAtV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineRestrictedCFMaxLowerTransportV1

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictedCFAtV1.StickyScaleCover

noncomputable section

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The original worst-parent normalized scalar is no larger than that of
the fully restricted reindexing.  This is the only direction needed to
transport a genuine lower barrier into the assembly cover. -/
theorem parentNormalizedFiberCFMax_le_activeFineRestricted
    (S : StickyScaleCover fine rho) :
    parentNormalizedFiberCFMax S ≤
      parentNormalizedFiberCFMax (activeFineRestrictedScaleCover S) := by
  unfold parentNormalizedFiberCFMax
  apply iSup_le
  intro k
  let q : {q // q ∈ (activeFineRestrictedScaleCover S).activeCoarse} :=
    ⟨(restrictedCoarseEquivActive S).symm k, by
      rw [activeFineRestrictedScaleCover_activeCoarse]
      exact Finset.mem_univ _⟩
  have hq : restrictedCoarseEquivActive S q.1 = k :=
    (restrictedCoarseEquivActive S).apply_symm_apply k
  calc
    parentNormalizedFiberCFAt S k =
        parentNormalizedFiberCFAt S
          (restrictedCoarseEquivActive S q.1) := by rw [hq]
    _ = parentNormalizedFiberCFAt (activeFineRestrictedScaleCover S) q :=
      (activeFineRestricted_parentNormalizedFiberCFAt_eq S q).symm
    _ ≤ ⨆ q : {q // q ∈
        (activeFineRestrictedScaleCover S).activeCoarse},
          parentNormalizedFiberCFAt (activeFineRestrictedScaleCover S) q :=
      le_iSup _ q

#print axioms parentNormalizedFiberCFMax_le_activeFineRestricted

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineRestrictedCFMaxLowerTransportV1
