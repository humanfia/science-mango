import Family8Grounding.Family8StickyFiberContractedJohnNormalizedFreshClosedLossV1
import Family8Grounding.Family8StickyFiberContractedJohnProxyKatzTaoV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyFiberContractedJohnGlobalNormalizedFreshV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyFiberContractedJohnProxyKatzTaoV2
open Family8StickyFiberContractedJohnNormalizedFreshClosedLossV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Global Katz--Tao to automatic normalized fresh selection

The affine-preimage/volume-ratio producer is composed with the canonical
proxy fresh selection.  The proxy Katz--Tao hypothesis is no longer exposed:
global control of the original fine family is the only Katz--Tao input.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The explicit proxy Katz--Tao constant is finite whenever the global
source constant is finite and the original tube scale is positive. -/
theorem stickyFiberContractedJohnProxyKatzTaoConstant_ne_top
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hdelta : 0 < delta)
    (k : {k // k ∈ S.activeCoarse}) {C : ENNReal}
    (hCfinite : C ≠ ∞) :
    stickyFiberContractedJohnProxyKatzTaoConstant
      S hrho hrhoOne k C ≠ ∞ := by
  unfold stickyFiberContractedJohnProxyKatzTaoConstant
  apply ENNReal.div_ne_top
  · apply ENNReal.mul_ne_top
    · unfold contractedJohnProxyVolumeRatio
      apply ENNReal.div_ne_top
      · exact ENNReal.mul_ne_top (by norm_num)
          (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      · exact ENNReal.div_ne_zero.mpr
          ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩
    · exact hCfinite
  · exact (affineJacobian_pos
      (stickyFiberContractedJohnAffineEquiv
        S hrho hrhoOne k)).ne'

/-- A global Katz--Tao family admits, on every active Sticky fibre, a
literal admissible normalized proxy refinement with explicit closed loss. -/
theorem exists_stickyFiberContractedJohn_global_normalizedFresh_closedLoss
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho) (k : {k // k ∈ S.activeCoarse})
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C fine.bodyFamily) :
    let Cproxy := stickyFiberContractedJohnProxyKatzTaoConstant
      S hrho hrhoOne k C
    let D := stickyFiberContractedJohnProxyDatum S Y hrho hrhoOne k
    let closedLoss : ENNReal := 480000 * (128 * Cproxy) + 2
    exists selected : Finset {i // i ∈ S.fiber k.1},
      selected.Nonempty ∧
      (restrictActualTubeDatum (eighthNormalizedDatum D) selected).IsAdmissible ∧
      (Fintype.card {i // i ∈ S.fiber k.1} : ENNReal) <=
        closedLoss * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum D).shading.shadingMass <=
        closedLoss *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass ∧
      IsKatzTao (128 * Cproxy)
        (restrictActualTubeDatum
          (eighthNormalizedDatum D) selected).family.bodyFamily ∧
      (stickyFiberSourceShading S Y k.1).averageMultiplicity <=
        closedLoss *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.averageMultiplicity := by
  dsimp only
  let Cproxy := stickyFiberContractedJohnProxyKatzTaoConstant
    S hrho hrhoOne k C
  have hCproxyfinite : Cproxy ≠ ∞ :=
    stickyFiberContractedJohnProxyKatzTaoConstant_ne_top
      S hrho hrhoOne hdelta k hCfinite
  have hproxyKT : IsKatzTao Cproxy
      (stickyFiberContractedJohnProxyDatum
        S Y hrho hrhoOne k).family.bodyFamily := by
    change IsKatzTao Cproxy
      (stickyFiberContractedJohnProxyFamily
        S hrho hrhoOne k).bodyFamily
    exact stickyFiberContractedJohnProxyFamily_isKatzTao_of_global
      S Y hrho hrhoOne hdelta hdeltaHalf hdeltaRho k hKT
  simpa only [Cproxy] using
    (exists_stickyFiberContractedJohn_normalizedFresh_closedLoss_of_isKatzTao
      S Y hdelta hrho hrhoOne hdeltaRho k hCproxyfinite hproxyKT)

#print axioms stickyFiberContractedJohnProxyKatzTaoConstant_ne_top
#print axioms exists_stickyFiberContractedJohn_global_normalizedFresh_closedLoss

end

end Family8StickyFiberContractedJohnGlobalNormalizedFreshV1
