import Family8Grounding.Family8StickyScaleCoverActiveFineSameCoarseFiberBodyV1
import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineSameCoarseCFAtV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseCoverV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseFiberEquivV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineSameCoarseFiberBodyV1.StickyScaleCover
open Family8StickySelectedParentGreedyBlockFrostmanV3

noncomputable section

/-! # Parent-normalized Frostman invariance under active-fine reindexing -/

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- At a fixed literal parent, normalized fibre concentration is invariant
under insertion of active-membership proofs into the fine index. -/
theorem activeFineSameCoarse_parentNormalizedFiberCFAt_eq
    (S : StickyScaleCover fine rho) (k : {k // k ∈ S.activeCoarse}) :
    parentNormalizedFiberCFAt (activeFineSameCoarseCover S) k =
      parentNormalizedFiberCFAt S k := by
  unfold parentNormalizedFiberCFAt
  exact canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
    (e := activeFineSameCoarseFiberEquiv S k.1)
    (F := (activeFineSameCoarseCover S).fiberFamily k.1)
    (G := S.fiberFamily k.1)
    (hbody := activeFineSameCoarseFiberEquiv_body S k.1)
    (K := S.activeCoarseFamily k)

#print axioms activeFineSameCoarse_parentNormalizedFiberCFAt_eq

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineSameCoarseCFAtV3
