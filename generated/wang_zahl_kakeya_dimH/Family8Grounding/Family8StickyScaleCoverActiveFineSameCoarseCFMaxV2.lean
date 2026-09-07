import Family8Grounding.Family8StickyScaleCoverActiveFineSameCoarseCFAtV3

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineSameCoarseCFMaxV2

open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseCoverV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseCFAtV3.StickyScaleCover

noncomputable section

/-! # Worst-parent normalized Frostman invariance -/

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The finite worst-parent normalized constant is unchanged by the
same-coarse active-fine reindexing.  Pointwise equality is lifted through the
supremum as a function congruence, avoiding a duplicated order proof. -/
theorem activeFineSameCoarse_parentNormalizedFiberCFMax_eq
    (S : StickyScaleCover fine rho) :
    parentNormalizedFiberCFMax (activeFineSameCoarseCover S) =
      parentNormalizedFiberCFMax S := by
  unfold parentNormalizedFiberCFMax
  apply congrArg
    (fun f : {k // k ∈ S.activeCoarse} → ENNReal => ⨆ k, f k)
  funext k
  exact activeFineSameCoarse_parentNormalizedFiberCFAt_eq S k

#print axioms activeFineSameCoarse_parentNormalizedFiberCFMax_eq

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineSameCoarseCFMaxV2
