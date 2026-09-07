import Family8Grounding.Family8SelectedParentCardWeightedCordobaCoreV2
import Family8Grounding.Family8SelectedParentBucketContainerJacobianEnvelopeV3
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV10
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentCardWeightedFixedEnvelopeLogAbsorptionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentBucketContainerJacobianEnvelopeV3
open Family8SelectedParentCardWeightedCordobaCoreV2
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Fixed-container and side-log absorption for the one-count core

The actual normalized John-container volume contributes its literal affine
Jacobian and a fixed `2304^3`.  The fixed constant and side logarithm are
absorbed into an arbitrarily small negative power, leaving only
`loss * activeCard * KT`.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem relativeScaled_cardWeightedCordobaCore_le_of_residualEnvelope
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 → Int) (KT : ENNReal)
    (tubesPerPlank : Nat)
    {capBound relativeSquare sourcePower : ENNReal}
    {lossEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hrhoThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hscalar :
      capBound *
          ((rho : ENNReal) ^ (-(lossEta + absorbEta)) *
            ((loss : ENNReal) *
              (Fintype.card (ActiveParentIndex S) : ENNReal) * KT)) ≤
        relativeSquare *
          (sourcePower *
            proposition66AInnerFactor rho
              (bucketShortA label) (bucketShortB label)
              tubesPerPlank epsilon beta)) :
    capBound *
        ((rho : ENNReal) ^ (-lossEta) *
          selectedParentCardWeightedCordobaCoreBudget
            D S hrho P k r A label KT) ≤
      relativeSquare *
        ((affineJacobian
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label) * sourcePower) *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta) := by
  let J : ENNReal := affineJacobian
    (bucketNormalizedAffineEquiv
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      label)
  let residual : ENNReal :=
    (loss : ENNReal) *
      (Fintype.card (ActiveParentIndex S) : ENNReal) * KT
  have hvolume :=
    selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_fixed
      hD.contained_in_unit_ball S hrho hrhoOne P k r hr label
  have hfinite :
      ((2 : ENNReal) * (2304 : ENNReal) ^ 3) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hlog :
      ((2 : ENNReal) * (2304 : ENNReal) ^ 3) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) ≤
        (rho : ENNReal) ^ (-absorbEta) :=
    fixedConstant_mul_selectedParentLogarithmicSideBucketLoss_le_rpow
      (rho := rho)
      (fixedConstant := (2 : ENNReal) * (2304 : ENNReal) ^ 3)
      (lossEta := absorbEta) hfinite habsorbEta hrho hrhoThreshold
  have hcore :
      selectedParentCardWeightedCordobaCoreBudget
          D S hrho P k r A label KT ≤
        J * ((rho : ENNReal) ^ (-absorbEta) * residual) := by
    change
      (((loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal)) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) * 2) *
        (KT * volume
          (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space)) ≤ _
    calc
      (((loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal)) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) * 2) *
        (KT * volume
          (selectedParentBucketNormalizedJohnContainer
            S hrho P k r label : Set Space)) ≤
        (((loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal)) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) * 2) *
        (KT * (J * (2304 : ENNReal) ^ 3)) := by
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hvolume)
      _ = J * (residual *
          (((2 : ENNReal) * (2304 : ENNReal) ^ 3) *
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal))) := by
        dsimp only [residual]
        ac_rfl
      _ ≤ J * (residual * (rho : ENNReal) ^ (-absorbEta)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hlog)
      _ = J * ((rho : ENNReal) ^ (-absorbEta) * residual) := by ac_rfl
  have hpow :
      (rho : ENNReal) ^ (-lossEta) *
          (rho : ENNReal) ^ (-absorbEta) =
        (rho : ENNReal) ^ (-(lossEta + absorbEta)) := by
    rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hrho.ne') (by simp)]
    congr 1
    ring
  calc
    capBound * ((rho : ENNReal) ^ (-lossEta) *
        selectedParentCardWeightedCordobaCoreBudget
          D S hrho P k r A label KT) ≤
      capBound * ((rho : ENNReal) ^ (-lossEta) *
        (J * ((rho : ENNReal) ^ (-absorbEta) * residual))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hcore)
    _ = J * (capBound *
        (((rho : ENNReal) ^ (-lossEta) *
          (rho : ENNReal) ^ (-absorbEta)) * residual)) := by ac_rfl
    _ = J * (capBound *
        ((rho : ENNReal) ^ (-(lossEta + absorbEta)) * residual)) := by
      rw [hpow]
    _ ≤ J * (relativeSquare *
        (sourcePower * proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta)) := by
      exact mul_le_mul' le_rfl (by simpa only [residual] using hscalar)
    _ = relativeSquare * ((J * sourcePower) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta) := by ac_rfl

#print axioms relativeScaled_cardWeightedCordobaCore_le_of_residualEnvelope

end
end Family8SelectedParentCardWeightedFixedEnvelopeLogAbsorptionV1
