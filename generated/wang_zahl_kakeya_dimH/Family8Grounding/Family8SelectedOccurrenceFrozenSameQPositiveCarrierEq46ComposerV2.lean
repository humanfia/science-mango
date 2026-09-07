import Family8Grounding.Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
import Mathlib.Tactic

/-!
# The selected positive-carrier label: conditional product-form Equation (46)

`V1` exposed a single-label Equation (46) budget, but that budget asked for
the numerator *after* the carrier floor had already been removed to be bounded
by the source factor.  Here that budget is factored into a clean-carrier local
power comparison and a selected-source payment which retains the literal
Proposition 6.6(A) inner factor on both sides.

This file keeps the common positive finite source factor

`J * (sourceDensity * (delta^2 / 2))`

through the Cordoba estimate.  The quantitative carrier floor is paid by the
literal `positiveCarrierShading` returned by the same-`q` payment theorem.  A
local endpoint power estimate is then used before the common source factor is
cancelled.

There remains an explicit conditional scalar premise: the selected source
density has to pay the dyadic and frozen-selection losses after multiplication
by the same inner factor.  It is stated separately as
`SelectedOccurrenceFrozenSameQPositiveCarrierSourcePowerPayment`; in
particular it is not hidden inside an all-label Equation (46) hypothesis.  A
later cross-multiplied final composer may be cheaper than this standalone seam.

The existing
`sameScale_packingKT_sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_localPower`
cannot be applied literally here: that theorem hard-codes the raw plank-bucket
shading, whereas the payment theorem and its Cordoba estimate use
`positiveCarrierShading` of that bucket.  The first theorem below is the exact
clean-carrier analogue, with the same fixed endpoint power input.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV2

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
open Family8GreedyHighPrefixSameOccurrenceCarrierFloorCancellationV1
open Family8GreedyHighPrefixSameOccurrenceProp66AInnerBridgeV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8Prop66AOuterInnerProductAlgebraV1
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
set_option maxHeartbeats 7000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The honest source-density payment left after the endpoint KT power has
been proved.  It retains the selected inner factor on both sides, without
assuming that factor is positive or finite. -/
def SelectedOccurrenceFrozenSameQPositiveCarrierSourcePowerPayment
    (bucketCoefficient positiveCarrierLoss sourceDensity sourcePower
      innerLoss innerFactor : ENNReal) : Prop :=
  bucketCoefficient * (positiveCarrierLoss * (sourcePower * innerFactor)) <=
    sourceDensity * ((delta : ENNReal) ^ 2 / 2) *
      (innerLoss * innerFactor)

/-- Discharge the selected-source payment from an honest lower bound for the
literal selected source density and the remaining pure scalar ledger.  The
input `hdensity` can be supplied by the endpoint density-floor theorem or by
`source_shadingDensity_div_loss_le_restrictActualTubeDatum`. -/
theorem
    SelectedOccurrenceFrozenSameQPositiveCarrierSourcePowerPayment.of_densityFloor
    (bucketCoefficient positiveCarrierLoss sourceDensity sourcePower
      innerLoss innerFactor densityFloor : ENNReal)
    (hdensity : densityFloor <= sourceDensity)
    (hscalar :
      bucketCoefficient * (positiveCarrierLoss *
        (sourcePower * innerFactor)) <=
        densityFloor * ((delta : ENNReal) ^ 2 / 2) *
          (innerLoss * innerFactor)) :
    SelectedOccurrenceFrozenSameQPositiveCarrierSourcePowerPayment
      (delta := delta) bucketCoefficient positiveCarrierLoss sourceDensity
        sourcePower innerLoss innerFactor := by
  exact hscalar.trans
    (mul_le_mul' (mul_le_mul' hdensity le_rfl) le_rfl)

/-- Clean-positive-carrier version of the endpoint same-scale local power
bridge.  The raw/clean carrier-floor mismatch is avoided by accepting the
literal cleaned shading produced by the payment theorem. -/
theorem
    sameScale_packingKT_positiveCarrier_sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_localPower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover (fullRefinementDatum D).family delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity loss : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (_Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P q).fiber))
    {carrierIndex : Type} [Fintype carrierIndex]
    [DecidableEq carrierIndex]
    {carrierFamily : ConvexFamily carrierIndex}
    (Yclean : Shading carrierFamily)
    (tubesPerPlank : Nat)
    {outputEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta)
    (hfloor :
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr)
            label) *
          (sourceDensity * ((delta : ENNReal) ^ 2 / 2)) <=
        loss * quantitativeCarrierFloor Yclean)
    (hpower :
      (delta : ENNReal) ^ (-(2 + absorbEta)) <=
        (delta : ENNReal) ^ (2 * outputEta) *
          proposition66AInnerFactor delta
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta) :
    (affineJacobian
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr)
          label) *
        (sourceDensity * ((delta : ENNReal) ^ 2 / 2))) *
        (endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Yclean))) <=
      loss *
        (affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr)
            label) *
          ((delta : ENNReal) ^ (2 * outputEta) *
            proposition66AInnerFactor delta
              (bucketShortA label) (bucketShortB label)
              tubesPerPlank epsilon beta)) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hD.delta_pos P q) r hr
  let KT := endpointIdentitySourceTauPackingKatzTaoConstant delta delta
  have hcancel :=
    quantitativeCarrierFloorDensity_mul_thresholdedCordobaScale_le
      Yclean (affineJacobian (bucketNormalizedAffineEquiv e label))
      sourceDensity loss KT delta r (sideShapeUpper label 2) hfloor
  have hfixed :=
    endpointIdentitySourceTauPackingKatzTaoConstant_fixedResidual_of_power
      hD.delta_pos habsorbEta hsmall delta
      (bucketShortA label) (bucketShortB label) tubesPerPlank hpower
  have hgeometry :=
    thresholdedCordobaNumerator_le_sameBucketJacobian_fixed
      (fine := (fullRefinementDatum D).family)
      (rho := delta)
      (fun i => hD.contained_in_unit_ball i)
      S hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      P q r hr label
  have hresidual :
      KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)) <=
        affineJacobian (bucketNormalizedAffineEquiv e label) *
          ((delta : ENNReal) ^ (2 * outputEta) *
            proposition66AInnerFactor delta
              (bucketShortA label) (bucketShortB label)
              tubesPerPlank epsilon beta) := by
    calc
      KT * (certifiedPlankThresholdedAngleScaleCap 576 *
          ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3)) <=
        KT * (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (2304 : ENNReal) ^ 3)) := mul_le_mul' le_rfl hgeometry
      _ = affineJacobian (bucketNormalizedAffineEquiv e label) *
          (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
            (2304 : ENNReal) ^ 3)) := by ac_rfl
      _ <= affineJacobian (bucketNormalizedAffineEquiv e label) *
          ((delta : ENNReal) ^ (2 * outputEta) *
            proposition66AInnerFactor delta
              (bucketShortA label) (bucketShortB label)
              tubesPerPlank epsilon beta) := mul_le_mul' le_rfl hfixed
  dsimp only [e, KT] at hcancel hresidual ⊢
  exact hcancel.trans (mul_le_mul' le_rfl hresidual)

/-- Conditional fixed-label standalone composer.

Unlike `V1`, this theorem consumes the payment's `hcordoba` and `hfloor`
fields, never its already floor-cancelled `hcancel` field.  Its two explicit
scalar premises are the local endpoint power and the product-form selected-
source-density payment; this theorem does not claim that either premise is
automatic. -/
theorem selectedOccurrenceFrozenSameQPositiveCarrier_finalFiberAverage_le_inner_of_localPower
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
    (hsource : source.shadingMass ≠ 0)
    (innerLoss : ENNReal) (tubesPerPlank : Nat)
    {outputEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta)
    (hpower :
      (delta : ENNReal) ^ (-(2 + absorbEta)) <=
        (delta : ENNReal) ^ (2 * outputEta) *
          proposition66AInnerFactor delta
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)
    (hsourcePower :
      let bucketCoefficient : ENNReal :=
        (selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
          (2 *
            ((certifiedPlankThresholdedAngleBucketLoss
              (bucketShortA label) (bucketShortB label) : Nat) : ENNReal))
      SelectedOccurrenceFrozenSameQPositiveCarrierSourcePowerPayment
        (delta := delta) bucketCoefficient
          (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P)
          source.shadingDensity ((delta : ENNReal) ^ (2 * outputEta))
          innerLoss (proposition66AInnerFactor delta
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta)) :
    (finalFiberShading A (some q)).averageMultiplicity <=
      innerLoss * proposition66AInnerFactor delta
        (bucketShortA label) (bucketShortB label)
        tubesPerPlank epsilon beta := by
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
  have hsourcePower' : bucketCoefficient *
      (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
        ((delta : ENNReal) ^ (2 * outputEta) * innerFactor)) <=
      source.shadingDensity * ((delta : ENNReal) ^ 2 / 2) *
        (innerLoss * innerFactor) := by
    simpa only [bucketCoefficient,
      SelectedOccurrenceFrozenSameQPositiveCarrierSourcePowerPayment]
      using hsourcePower
  have hpaid : bucketCoefficient *
      (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          ((delta : ENNReal) ^ (2 * outputEta) * innerFactor))) <=
      sourceFactor * (innerLoss * innerFactor) := by
    calc
      bucketCoefficient *
          (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
            (affineJacobian (bucketNormalizedAffineEquiv e label) *
              ((delta : ENNReal) ^ (2 * outputEta) * innerFactor))) =
        affineJacobian (bucketNormalizedAffineEquiv e label) *
          (bucketCoefficient *
            (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
              ((delta : ENNReal) ^ (2 * outputEta) * innerFactor))) := by
            ac_rfl
      _ <= affineJacobian (bucketNormalizedAffineEquiv e label) *
          (source.shadingDensity * ((delta : ENNReal) ^ 2 / 2) *
            (innerLoss * innerFactor)) := mul_le_mul' le_rfl hsourcePower'
      _ = sourceFactor * (innerLoss * innerFactor) := by
        dsimp only [sourceFactor]
        unfold selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
        dsimp only
        ac_rfl
  have hscaled : sourceFactor * Z.averageMultiplicity <=
      sourceFactor * (innerLoss * innerFactor) := by
    calc
      sourceFactor * Z.averageMultiplicity <=
          sourceFactor * (bucketCoefficient * (KT * floorScale)) :=
        mul_le_mul' le_rfl hZ
      _ = bucketCoefficient * (sourceFactor * (KT * floorScale)) := by
        ac_rfl
      _ <= bucketCoefficient *
          (selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
            (affineJacobian (bucketNormalizedAffineEquiv e label) *
              ((delta : ENNReal) ^ (2 * outputEta) * innerFactor))) :=
        mul_le_mul' le_rfl hkernel'
      _ <= sourceFactor * (innerLoss * innerFactor) := hpaid
  have hsourceFactor0 : sourceFactor ≠ 0 := by
    dsimp only [sourceFactor]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_zero
      S hD.delta_pos P q source r hr label hsource
  have hsourceFactorTop : sourceFactor ≠ ∞ := by
    dsimp only [sourceFactor]
    exact selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor_ne_top
      S hD.delta_pos P q source r hr label hsource
  have hinner : Z.averageMultiplicity <= innerLoss * innerFactor := by
    apply (ENNReal.mul_le_mul_iff_right
      hsourceFactor0 hsourceFactorTop).mp
    exact hscaled
  calc
    (finalFiberShading A (some q)).averageMultiplicity =
        Z.averageMultiplicity := by
      symm
      simpa only [Z] using
        (selectedOccurrenceFrozenFinalFiberBlockShading_averageMultiplicity_eq
          P R A q hq)
    _ <= innerLoss * innerFactor := hinner
    _ = innerLoss * proposition66AInnerFactor delta
        (bucketShortA label) (bucketShortB label)
        tubesPerPlank epsilon beta := rfl

#print axioms SelectedOccurrenceFrozenSameQPositiveCarrierSourcePowerPayment
#print axioms
  sameScale_packingKT_positiveCarrier_sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_localPower
#print axioms
  selectedOccurrenceFrozenSameQPositiveCarrier_finalFiberAverage_le_inner_of_localPower

end
end Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV2
