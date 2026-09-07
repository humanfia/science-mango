import Family8Grounding.Family8SelectedParentCombinedLogLossPowerAbsorptionV3
import Family8Grounding.Family8SelectedParentExactAssemblyProp66AConnectorV3
import Mathlib.Tactic

/-!
# Removing both logarithmic losses from the selected-parent Córdoba scalar, V2

Canonical successor to V1.  The missing actual bucket namespaces and the
fixed angle-cap finiteness proof are supplied explicitly.  The literal
selected-parent endpoint contains the cubic side-label count, thresholded
angle-row count, and fixed certified-plank cap.  They are absorbed into an
arbitrarily small negative power of `rho`, leaving only the Katz--Tao
constant and genuine normalized-volume / popular-mass quotient.

No desired multiplicity conclusion is assumed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentLogarithmicCordobaCoreV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentCombinedLogLossPowerAbsorptionV3
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The non-logarithmic core of the actual selected-parent fine-level
Córdoba scalar. -/
noncomputable def selectedParentFineLevelCordobaCore
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  KT *
    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
      (Ybucket.shadingMass /
        (((selectedParentPlankBucketIndices e S B hrho label).card :
          ENNReal) * 2)))

/-- Pure commutative-semiring rearrangement used to remove both logarithmic
losses without touching the genuine geometric quotient. -/
theorem logarithmicCordobaScalar_le_rpow_mul
    {sideLoss angleLoss cap KT quotient power : ENNReal}
    (hloss : sideLoss * ((4 * cap) * angleLoss) ≤ power) :
    sideLoss * (2 * ((2 * angleLoss) * KT * (cap * quotient))) ≤
      power * (KT * quotient) := by
  calc
    sideLoss * (2 * ((2 * angleLoss) * KT * (cap * quotient))) =
        (sideLoss * ((4 * cap) * angleLoss)) *
          (KT * quotient) := by ring
    _ ≤ power * (KT * quotient) := mul_le_mul' hloss le_rfl

/-- Both actual dyadic losses and the fixed certified-plank cap are absorbed,
leaving precisely the non-logarithmic selected-parent Córdoba core. -/
theorem selectedParentFineLevelLogarithmicCordobaRHS_le_rpow_mul_core
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        (4 * certifiedPlankThresholdedAngleScaleCap 576)
        (lossEta / 4)) :
    selectedParentFineLevelLogarithmicCordobaRHS
        D S hrho P k r hr A label KT ≤
      (rho : ENNReal) ^ (-lossEta) *
        selectedParentFineLevelCordobaCore
          D S hrho P k r hr A label KT := by
  have hfixedFinite :
      4 * certifiedPlankThresholdedAngleScaleCap 576 ≠ ∞ := by
    unfold certifiedPlankThresholdedAngleScaleCap
    apply ENNReal.mul_ne_top
    · norm_num
    · apply max_ne_top
      · norm_num
      · apply ENNReal.mul_ne_top
        · norm_num
        · apply ENNReal.inv_ne_top.mpr
          norm_num
  have hlogs := fixedConstant_mul_combinedSelectedParentLogLoss_le_rpow
    (rho := rho)
    (fixedConstant := 4 * certifiedPlankThresholdedAngleScaleCap 576)
    (lossEta := lossEta) hfixedFinite hlossEta hrho hrhoHalf
    hsideThreshold hangleThreshold
  apply logarithmicCordobaScalar_le_rpow_mul at hlogs
  simpa only [selectedParentFineLevelLogarithmicCordobaRHS,
    selectedParentFineLevelCordobaCore, Nat.cast_mul,
    Nat.cast_ofNat] using hlogs

#print axioms logarithmicCordobaScalar_le_rpow_mul
#print axioms
  selectedParentFineLevelLogarithmicCordobaRHS_le_rpow_mul_core

end

end Family8SelectedParentLogarithmicCordobaCoreV2
