import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictedFiberBodyV1
import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8StickyScaleCoverActiveFineRestrictedCFAtV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineRestrictedFiberEquivV4.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictedFiberBodyV1.StickyScaleCover
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover

noncomputable section

namespace StickyScaleCover

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- At corresponding active parents, the normalized fibre Frostman scalar is
unchanged by the full active-fine/active-coarse reindexing. -/
theorem activeFineRestricted_parentNormalizedFiberCFAt_eq
    (S : StickyScaleCover fine rho)
    (q : {q // q ∈ (activeFineRestrictedScaleCover S).activeCoarse}) :
    parentNormalizedFiberCFAt (activeFineRestrictedScaleCover S) q =
      parentNormalizedFiberCFAt S
        (restrictedCoarseEquivActive S q.1) := by
  unfold parentNormalizedFiberCFAt
  exact canonicalFrostmanConstant_eq_of_bodyPreservingEquiv
    (e := activeFineRestrictedFiberEquiv S q.1)
    (F := (activeFineRestrictedScaleCover S).fiberFamily q.1)
    (G := S.fiberFamily (restrictedCoarseEquivActive S q.1).1)
    (hbody := activeFineRestrictedFiberEquiv_body S q.1)
    (K := S.activeCoarseFamily (restrictedCoarseEquivActive S q.1))

#print axioms activeFineRestricted_parentNormalizedFiberCFAt_eq

end StickyScaleCover

end
end Family8StickyScaleCoverActiveFineRestrictedCFAtV1
