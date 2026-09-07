import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV2
import Mathlib.Tactic

/-!
# Endpoint local-power cross composer for one selected positive carrier label

This theorem stops before any source-density division.  For the fixed
occurrence and fixed label returned by the same-`q` payment it proves

`sourceFactor * finalFiberAverage <=
  bucketCoefficient * (positiveCarrierLoss *
    (Jacobian * (sourcePower * proposition66AInnerFactor)))`.

The clean carrier floor is paid on the same literal `Yclean`, and the endpoint
local KT power is inserted, but the positive finite `sourceFactor` is not
cancelled.  Thus no second joint/winner retention loss and no separate
`delta^2 / sourceDensity` payment is introduced at this node.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV2
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
set_option maxHeartbeats 7000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Exact right side of the fixed-label local-power cross estimate. -/
noncomputable def selectedOccurrenceFrozenSameQPositiveCarrierLocalPowerCrossRHS
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (sourcePower innerFactor : ENNReal) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
  let bucketCoefficient : ENNReal :=
    (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
      (2 *
        ((certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : Nat) : ENNReal))
  bucketCoefficient *
    (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
      (affineJacobian (bucketNormalizedAffineEquiv e label) *
        (sourcePower * innerFactor)))

/-- Weak endpoint fixed-label producer: it consumes the payment's clean
`hcordoba` and clean `hfloor`, inserts only the local KT power comparison, and
retains the complete source factor on the left. -/
theorem
    selectedOccurrenceFrozenSameQPositiveCarrier_sourceFactor_mul_finalFiberAverage_le_localPowerCrossRHS
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover (fullRefinementDatum D).family delta)
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
              (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr)
            S (blockAt S.activeCoarseFamily P q).fiber hD.delta_pos p)
          label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr)
              label)
            S (blockAt S.activeCoarseFamily P q).fiber p))
    (hcordoba :
      let B := (blockAt S.activeCoarseFamily P q).fiber
      let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr
      let Yraw := selectedParentArbitraryPlankBucketShading
        e S B hD.delta_pos label Z
      let Yclean := positiveCarrierShading Yraw
      let hplankPos : forall t,
          IsPlank 576 (bucketShortA label) (bucketShortB label)
            (quantitativePositiveCarrierFamily Yclean t) := fun t =>
        selectedParentPlankBucket_isPlank
          e S B hD.delta_pos label hplank t.1.1
      let cert := chosenPlankCertificate hplankPos
      Z.averageMultiplicity <=
        (selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert)
              (endpointIdentitySourceTauPackingKatzTaoConstant delta delta)
              (certifiedPlankThresholdedAngleScaleCap 576 *
                (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                    ENNReal) ^ 3) /
                  quantitativeCarrierFloor Yclean))))
    (hfloor :
      let B := (blockAt S.activeCoarseFamily P q).fiber
      let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr
      let Yraw := selectedParentArbitraryPlankBucketShading
        e S B hD.delta_pos label Z
      let Yclean := positiveCarrierShading Yraw
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (source.shadingDensity * ((delta : ENNReal) ^ 2 / 2)) <=
        selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
          quantitativeCarrierFloor Yclean)
    (tubesPerPlank : Nat)
    {outputEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta)
    (hpower :
      (delta : ENNReal) ^ (-(2 + absorbEta)) <=
        (delta : ENNReal) ^ (2 * outputEta) *
          proposition66AInnerFactor delta
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta) :
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
        S hD.delta_pos P q source r hr label *
      (finalFiberShading A (some q)).averageMultiplicity <=
        selectedOccurrenceFrozenSameQPositiveCarrierLocalPowerCrossRHS
          S hD.delta_pos P q r hr label
            ((delta : ENNReal) ^ (2 * outputEta))
            (proposition66AInnerFactor delta
              (bucketShortA label) (bucketShortB label)
              tubesPerPlank epsilon beta) := by
  let B := (blockAt S.activeCoarseFamily P q).fiber
  let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr
  let Yraw := selectedParentArbitraryPlankBucketShading
    e S B hD.delta_pos label Z
  let Yclean := positiveCarrierShading Yraw
  let hplankPos : forall t,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Yclean t) := fun t =>
    selectedParentPlankBucket_isPlank
      e S B hD.delta_pos label hplank t.1.1
  let cert := chosenPlankCertificate hplankPos
  let KT := endpointIdentitySourceTauPackingKatzTaoConstant delta delta
  let floorScale : ENNReal :=
    certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
        quantitativeCarrierFloor Yclean)
  let bucketCoefficient : ENNReal :=
    (selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
      (2 *
        ((certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : Nat) : ENNReal))
  let sourceFactor : ENNReal :=
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
      S hD.delta_pos P q source r hr label
  let innerFactor : ENNReal := proposition66AInnerFactor delta
    (bucketShortA label) (bucketShortB label)
    tubesPerPlank epsilon beta
  have hcordoba' : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
        (2 * certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT floorScale) := by
    simpa only [B, Z, e, Yraw, Yclean, hplankPos, cert, KT, floorScale]
      using hcordoba
  have hexpand :
      (selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT floorScale) <=
        bucketCoefficient * (KT * floorScale) := by
    have h := loss_mul_two_mul_certifiedPlankDyadicFactor_le_explicit
      cert (selectedParentLogarithmicSideBucketLoss delta : ENNReal)
        KT floorScale
    calc
      (selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT floorScale) <=
        (selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
          (2 *
            (((certifiedPlankThresholdedAngleBucketLoss
              (bucketShortA label) (bucketShortB label) : Nat) : ENNReal) *
              KT * floorScale)) := h
      _ = bucketCoefficient * (KT * floorScale) := by
        dsimp only [bucketCoefficient]
        ac_rfl
  have hZ : Z.averageMultiplicity <=
      bucketCoefficient * (KT * floorScale) := hcordoba'.trans hexpand
  have hfloor' :
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (source.shadingDensity * ((delta : ENNReal) ^ 2 / 2)) <=
        selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
          quantitativeCarrierFloor Yclean := by
    simpa only [B, Z, e, Yraw, Yclean] using hfloor
  have hkernel :=
    sameScale_packingKT_positiveCarrier_sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_localPower
      D hD S P q source.shadingDensity
      (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P)
      r hr label Z Yclean tubesPerPlank habsorbEta hsmall hfloor' hpower
  have hkernel' : sourceFactor * (KT * floorScale) <=
      selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          ((delta : ENNReal) ^ (2 * outputEta) * innerFactor)) := by
    simpa only [sourceFactor,
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor,
      B, Z, e, Yraw, Yclean, KT, floorScale, innerFactor] using hkernel
  calc
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hD.delta_pos P q source r hr label *
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
          (affineJacobian (bucketNormalizedAffineEquiv e label) *
            ((delta : ENNReal) ^ (2 * outputEta) * innerFactor))) :=
      mul_le_mul' le_rfl hkernel'
    _ = selectedOccurrenceFrozenSameQPositiveCarrierLocalPowerCrossRHS
        S hD.delta_pos P q r hr label
          ((delta : ENNReal) ^ (2 * outputEta)) innerFactor := by
      dsimp only [
        selectedOccurrenceFrozenSameQPositiveCarrierLocalPowerCrossRHS,
        bucketCoefficient, e]

#print axioms selectedOccurrenceFrozenSameQPositiveCarrierLocalPowerCrossRHS
#print axioms
  selectedOccurrenceFrozenSameQPositiveCarrier_sourceFactor_mul_finalFiberAverage_le_localPowerCrossRHS

end
end Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV3
