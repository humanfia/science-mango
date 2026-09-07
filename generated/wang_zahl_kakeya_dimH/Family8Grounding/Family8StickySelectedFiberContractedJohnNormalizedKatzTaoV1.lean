import Family8Grounding.Family8StickySelectedFiberContractedJohnProxyKatzTaoV2
import Family8Grounding.Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
import Mathlib.Tactic

/-!
# Same-selected normalized contracted-John Katz--Tao endpoint

The source restriction is taken before the eighth normalization in the
proof, but its body family is definitionally the literal restriction of the
normalized datum used by the existing Frostman connector.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickySelectedFiberContractedJohnNormalizedKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FiniteRandomRigidMotionB2KatzTaoTransportV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickySelectedFiberContractedJohnProxyKatzTaoV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Low-CF source Katz--Tao control reaches the exact normalized selected
proxy body family consumed downstream, with the honest factor `128`. -/
theorem selectedFiberContractedJohn_restrictEighthNormalized_isKatzTao
    (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hdeltaRho : delta ≤ rho)
    (k : {k // k ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber k.1})
    {C : ENNReal}
    (hKT : IsKatzTao C
      (activeSubtypeFamily (S.fiberFamily k.1) selected)) :
    IsKatzTao
      (128 * stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne k C)
      (restrictActualTubeDatum
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            S Y hrho hrhoOne k)) selected).family.bodyFamily := by
  let D := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k
  have hproxyKT : IsKatzTao
      (stickyFiberContractedJohnProxyKatzTaoConstant
        S hrho hrhoOne k C)
      (restrictActualTubeDatum D selected).family.bodyFamily := by
    simpa only [D] using
      selectedFiberContractedJohnProxy_isKatzTao
        S Y hrho hrhoOne hdeltaPos hdeltaHalf hdeltaRho k selected hKT
  have hnormalized := eighthNormalizedDatum_isKatzTao
    (restrictActualTubeDatum D selected)
    (stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho)
    hproxyKT
  have hfamily :
      (eighthNormalizedDatum
        (restrictActualTubeDatum D selected)).family.bodyFamily =
      (restrictActualTubeDatum
        (eighthNormalizedDatum D) selected).family.bodyFamily := rfl
  rw [hfamily] at hnormalized
  simpa only [D] using hnormalized

#print axioms
  selectedFiberContractedJohn_restrictEighthNormalized_isKatzTao

end
end Family8StickySelectedFiberContractedJohnNormalizedKatzTaoV1
