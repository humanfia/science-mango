import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
import Mathlib.Tactic

/-!
# Cross-multiplied selected-label positive-carrier composer

This is the weakest fixed-label output of the same-`q` positive-carrier
payment.  It expands the certified Cordoba factor and pays the literal clean
carrier floor, but it does not cancel the common source factor and does not
ask for any local power or source-density lower bound.

The result is intended to be multiplied directly into the outer Equation
(45) / Proposition 6.6 product before the final Section 8 loss comparison.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyCordobaExpandedV5
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
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
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The one selected label returned by the payment theorem already gives a
fully cross-multiplied Equation (46) estimate.  No source factor is divided
out at this node. -/
theorem
    selectedOccurrenceFrozenSameQPositiveCarrier_sourceFactor_mul_finalFiberAverage_le_expandedEq46LHS
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily) {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) source rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length) (hq : q ∈ R)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hplank : forall p,
      p ∈ sideShapeBucket Finset.univ
          (fun p => selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
            S (blockAt S.activeCoarseFamily P q).fiber hrho p)
          label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P q) r hr)
              label)
            S (blockAt S.activeCoarseFamily P q).fiber p))
    (KT : ENNReal)
    (hcordoba :
      let B := (blockAt S.activeCoarseFamily P q).fiber
      let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
      let Yraw := selectedParentArbitraryPlankBucketShading
        e S B hrho label Z
      let Yclean := positiveCarrierShading Yraw
      let hplankPos : forall t,
          IsPlank 576 (bucketShortA label) (bucketShortB label)
            (quantitativePositiveCarrierFamily Yclean t) := fun t =>
        selectedParentPlankBucket_isPlank
          e S B hrho label hplank t.1.1
      let cert := chosenPlankCertificate hplankPos
      Z.averageMultiplicity <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT
              (certifiedPlankThresholdedAngleScaleCap 576 *
                (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                    ENNReal) ^ 3) /
                  quantitativeCarrierFloor Yclean))))
    (hcancel :
      let B := (blockAt S.activeCoarseFamily P q).fiber
      let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
      let Yraw := selectedParentArbitraryPlankBucketShading
        e S B hrho label Z
      let Yclean := positiveCarrierShading Yraw
      (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (source.shadingDensity * ((rho : ENNReal) ^ 2 / 2))) *
          (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                ENNReal) ^ 3) /
              quantitativeCarrierFloor Yclean))) <=
        selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
          (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
            ((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
              ENNReal) ^ 3)))) :
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
        S hrho P q source r hr label *
      (finalFiberShading A (some q)).averageMultiplicity <=
        selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
          S P r label KT := by
  let B := (blockAt S.activeCoarseFamily P q).fiber
  let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
  let Yraw := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let Yclean := positiveCarrierShading Yraw
  let hplankPos : forall t,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Yclean t) := fun t =>
    selectedParentPlankBucket_isPlank
      e S B hrho label hplank t.1.1
  let cert := chosenPlankCertificate hplankPos
  let floorScale : ENNReal :=
    certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
        quantitativeCarrierFloor Yclean)
  let numeratorScale : ENNReal :=
    certifiedPlankThresholdedAngleScaleCap 576 *
      ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)
  let bucketCoefficient : ENNReal :=
    (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
      (2 *
        ((certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : Nat) : ENNReal))
  let sourceFactor : ENNReal :=
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
      S hrho P q source r hr label
  have hcordoba' : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (2 * certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT floorScale) := by
    simpa only [B, Z, e, Yraw, Yclean, hplankPos, cert, floorScale]
      using hcordoba
  have hexpand :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT floorScale) <=
        bucketCoefficient * (KT * floorScale) := by
    have h := loss_mul_two_mul_certifiedPlankDyadicFactor_le_explicit
      cert (selectedParentLogarithmicSideBucketLoss rho : ENNReal)
        KT floorScale
    calc
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT floorScale) <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 *
            (((certifiedPlankThresholdedAngleBucketLoss
              (bucketShortA label) (bucketShortB label) : Nat) : ENNReal) *
              KT * floorScale)) := h
      _ = bucketCoefficient * (KT * floorScale) := by
        dsimp only [bucketCoefficient]
        ac_rfl
  have hZ : Z.averageMultiplicity <=
      bucketCoefficient * (KT * floorScale) := hcordoba'.trans hexpand
  have hcancel' : sourceFactor * (KT * floorScale) <=
      selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
        (KT * numeratorScale) := by
    simpa only [sourceFactor,
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor,
      B, Z, e, Yraw, Yclean, floorScale, numeratorScale] using hcancel
  calc
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr label *
        (finalFiberShading A (some q)).averageMultiplicity =
      sourceFactor * Z.averageMultiplicity := by
        rw [selectedOccurrenceFrozenFinalFiberBlockShading_averageMultiplicity_eq
          P R A q hq]
    _ <= sourceFactor * (bucketCoefficient * (KT * floorScale)) :=
      mul_le_mul' le_rfl hZ
    _ = bucketCoefficient * (sourceFactor * (KT * floorScale)) := by
      ac_rfl
    _ <= bucketCoefficient *
        (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
          (KT * numeratorScale)) := mul_le_mul' le_rfl hcancel'
    _ = selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
        S P r label KT := by
      dsimp only [bucketCoefficient, numeratorScale]
      unfold selectedOccurrenceFrozenSameQPositiveCarrierExpandedEq46LHS
      ac_rfl

#print axioms
  selectedOccurrenceFrozenSameQPositiveCarrier_sourceFactor_mul_finalFiberAverage_le_expandedEq46LHS

end
end Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV1
