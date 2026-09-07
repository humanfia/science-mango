import Family8Grounding.Family8SelectedParentAdaptiveInnerSourceReserveV1
import Mathlib.Tactic

/-!
# Absorbing the exact residual source-constant power

The local adaptive cap retains `C^(1-beta/2)` in the inner factor.  If the
actual source Katz--Tao constant satisfies its canonical delta-power upper
bound, the missing `C^(beta/2)` costs exactly the corresponding beta-half
delta exponent.  This is an exponent calculation, not a target-valued
premise.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentAdaptiveInnerSourcePowerReserveV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-- A delta-power upper envelope for `C` pays exactly for the residual
`C^(beta/2)` left after the adaptive cap enters the inner factor. -/
theorem sourceConstant_le_deltaBetaHalfLoss_mul_sourceReserve
    {delta : NNReal} {C : ENNReal} {coarseExponent beta : Real}
    (hdelta : 0 < delta)
    (hCpower : C <= (delta : ENNReal) ^ (-coarseExponent))
    (hbeta : 0 <= beta) (hbetaTwo : beta <= 2) :
    C <= (delta : ENNReal) ^ ((-coarseExponent) * (beta / 2)) *
      C ^ (1 - beta / 2) := by
  by_cases hC0 : C = 0
  · simp only [hC0, zero_le]
  · have hp : 0 <= 1 - beta / 2 := by linarith
    have hq : 0 <= beta / 2 := by linarith
    have hd0 : (delta : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr hdelta.ne'
    have hpowerTop : (delta : ENNReal) ^ (-coarseExponent) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top
    have hCtop : C ≠ ∞ := ne_top_of_le_ne_top hpowerTop hCpower
    have hrem : C ^ (beta / 2) <=
        (delta : ENNReal) ^ ((-coarseExponent) * (beta / 2)) := by
      calc
        C ^ (beta / 2) <=
            ((delta : ENNReal) ^ (-coarseExponent)) ^ (beta / 2) :=
          ENNReal.rpow_le_rpow hCpower hq
        _ = (delta : ENNReal) ^
            ((-coarseExponent) * (beta / 2)) :=
          (ENNReal.rpow_mul (delta : ENNReal)
            (-coarseExponent) (beta / 2)).symm
    calc
      C = C ^ (1 : Real) := by rw [ENNReal.rpow_one]
      _ = C ^ ((1 - beta / 2) + beta / 2) := by
        congr 1
        ring
      _ = C ^ (1 - beta / 2) * C ^ (beta / 2) :=
        ENNReal.rpow_add (1 - beta / 2) (beta / 2) hC0 hCtop
      _ <= C ^ (1 - beta / 2) *
          (delta : ENNReal) ^ ((-coarseExponent) * (beta / 2)) := by
        exact mul_le_mul' le_rfl hrem
      _ = (delta : ENNReal) ^ ((-coarseExponent) * (beta / 2)) *
          C ^ (1 - beta / 2) := by ac_rfl

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Same-object actual-bucket consequence.  The entire source constant is
now available at the price of the explicit beta-half delta power. -/
theorem selectedParent_sourceConstant_mul_scaleReserve_le_deltaBetaHalfLoss_mul_adaptiveActualInnerFactor
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : SelectedBucketOccupied S hrho P k r hr label)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label / 8 <= (1 / 100 : NNReal))
    (C : ENNReal) (coarseExponent epsilon beta : Real)
    (hCpower : C <= (delta : ENNReal) ^ (-coarseExponent))
    (hbeta : 0 <= beta) (hbetaTwo : beta <= 2) :
    C * ((rho : ENNReal) ^ (-epsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * beta))) <=
      (delta : ENNReal) ^ ((-coarseExponent) * (beta / 2)) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (centeredAdaptiveActualBucketFullFiberNatCap
            S hrho P k r hr label C) epsilon beta := by
  have hpowerTop : (delta : ENNReal) ^ (-coarseExponent) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hdelta.ne') ENNReal.coe_ne_top
  have hCfinite : C ≠ ∞ := ne_top_of_le_ne_top hpowerTop hCpower
  have hconstant :=
    sourceConstant_le_deltaBetaHalfLoss_mul_sourceReserve
      hdelta hCpower hbeta hbetaTwo
  have hinner := selectedParent_sourceScaleReserve_le_adaptiveActualInnerFactor
    S hrho P k r hr label hoccupied hdelta hdeltaHalf hsmallPacking
      C hCfinite epsilon beta hbetaTwo
  calc
    C * ((rho : ENNReal) ^ (-epsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * beta))) =
      ((rho : ENNReal) ^ (-epsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * beta))) * C := by ac_rfl
    _ <= ((rho : ENNReal) ^ (-epsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * beta))) *
        ((delta : ENNReal) ^ ((-coarseExponent) * (beta / 2)) *
          C ^ (1 - beta / 2)) := by
      exact mul_le_mul' le_rfl hconstant
    _ = (delta : ENNReal) ^ ((-coarseExponent) * (beta / 2)) *
        ((((rho : ENNReal) ^ (-epsilon / 2) *
          ((bucketShortB label : ENNReal) /
            (bucketShortA label : ENNReal)) *
        (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
          (2 - 3 * beta))) * C ^ (1 - beta / 2))) := by ac_rfl
    _ <= (delta : ENNReal) ^ ((-coarseExponent) * (beta / 2)) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (centeredAdaptiveActualBucketFullFiberNatCap
            S hrho P k r hr label C) epsilon beta := by
      exact mul_le_mul' le_rfl hinner

#print axioms sourceConstant_le_deltaBetaHalfLoss_mul_sourceReserve
#print axioms
  selectedParent_sourceConstant_mul_scaleReserve_le_deltaBetaHalfLoss_mul_adaptiveActualInnerFactor

end
end Family8SelectedParentAdaptiveInnerSourcePowerReserveV1
