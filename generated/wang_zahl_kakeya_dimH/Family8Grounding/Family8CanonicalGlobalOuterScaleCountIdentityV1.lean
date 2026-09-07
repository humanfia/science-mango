import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8CanonicalGlobalOuterScaleCountIdentityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-!
# Identify the literal global coarse factor with the Section 8 factor

The long-interval endpoint is written using the paper variable
`X = |T_b| b^2`.  This file records that its remaining `b`--`X` expression
is definitionally the existing loss-free Section 8 scale-count factor.
-/

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

theorem activeCoarseCardScaleMass_middleFactor_eq_sectionEight
    (S : StickyScaleCover fine rho) (gamma : Real) :
    (rho : ENNReal) ^ (-2 * gamma) *
        (activeCoarseCardScaleMass S : ENNReal) ^ (1 - gamma / 2) =
      sectionEightScaleCountFrostmanFactor
        rho 1 S.activeCoarse.card gamma := by
  simp only [sectionEightScaleCountFrostmanFactor,
    activeCoarseCardScaleMass, ENNReal.coe_one, div_one,
    ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_pow]
  rw [mul_comm (S.activeCoarse.card : ENNReal) ((rho : ENNReal) ^ 2)]

#print axioms activeCoarseCardScaleMass_middleFactor_eq_sectionEight

end
end Family8CanonicalGlobalOuterScaleCountIdentityV1
