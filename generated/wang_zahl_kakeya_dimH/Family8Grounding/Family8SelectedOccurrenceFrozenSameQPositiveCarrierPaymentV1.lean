import Family8Grounding.Family8ExactAssemblySameDataFiberBridgeV1
import Family8Grounding.Family8SameOccurrenceLocalCardCarrierFloorAdapterV1
import Family8Grounding.Family8SelectedOccurrenceExactOuterSurvivingDensePaymentV1
import Family8Grounding.Family8SelectedParentArbitraryBlockPositiveCarrierQuantitativeCordobaV1
import Mathlib.Tactic

/-!
# Same-occurrence compact carrier-floor payment

Start with the density-good surviving occurrence returned by the exact-outer
assembly.  Inside that fixed occurrence choose the actual weighted side label,
delete only the zero-volume carriers of its normalized bucket, and pay the
resulting quantitative carrier floor with the local surviving-fibre
cardinality.

The surviving cardinality is eliminated inside the scalar adapter.  Thus the
conclusion has no factor `R.card`, and neither the occurrence, assembly, nor
side label is reselected.  Equation (46) is needed only for the single label
returned here, not for every occupied label.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ActualRefinementSurvivingDenseFiberV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8ExactAssemblySameDataFiberBridgeV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SameOccurrenceLocalCardCarrierFloorAdapterV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceExactOuterSurvivingDensePaymentV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockPositiveCarrierQuantitativeCordobaV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
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
set_option maxHeartbeats 9000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The exact no-`R.card` loss after the frozen occurrence and its one
selected side bucket are paid.  The final factor two is the literal
quantitative-carrier-floor denominator. -/
def selectedOccurrenceFrozenSameQPositiveCarrierLoss
    (S : StickyScaleCover fine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ) : ENNReal :=
  ((frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) *
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) * 2

/-- One exact-outer density-good occurrence, followed inside that same
occurrence by its actual occupied side label and compact positive-carrier
Córdoba bucket.  The local surviving count cancels before the conclusion. -/
theorem exists_selectedOccurrence_exactOuter_survivingDense_sameQ_positiveCarrierPayment
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (hfineBucket : fineBucket ⊆ selectedOccurrenceFineIndices P R)
    (hYbucket :
      (IndexedShadingRefinement.restrictTo Y fineBucket).shading.shadingMass ≠
        0)
    (rFrozen : Real) (hrFrozen : 0 < rFrozen)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (selectedOccurrenceFactorization P R)
        (IndexedShadingRefinement.restrictTo Y fineBucket).shading rFrozen,
      A.loss = frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) ∧
      A.frozenCoarse =
          (selectedOccurrenceFactorization P R).inducedShading
            A.refinement.shading ∧
      ∃ q ∈ R,
        let source :=
          (IndexedShadingRefinement.restrictTo Y fineBucket).shading
        let B := (blockAt S.activeCoarseFamily P q).fiber
        let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
        let e := contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
        0 < volume (finalFiberShading A (some q)).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A (some q)).averageMultiplicity) ∧
        ∃ label : Fin 3 -> Int,
          label ∈ occupiedWeightBuckets
            (Finset.univ : Finset {p // p ∈ B})
            (fun p => sideShapeLabel
              (selectedParentLongRelabeledSide e S B hrho p)) ∧
          0 < bucketShortA label ∧
          bucketShortA label <= bucketShortB label ∧
          bucketShortB label <= 1 ∧
          ∃ hplank : forall p,
              p ∈ sideShapeBucket Finset.univ
                  (fun p => selectedParentLongRelabeledSide e S B hrho p)
                  label ->
                IsPlank 576 (bucketShortA label) (bucketShortB label)
                  (selectedParentAffineFamily
                    (bucketNormalizedAffineEquiv e label) S B p),
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
                        quantitativeCarrierFloor Yclean))) ∧
            affineJacobian (bucketNormalizedAffineEquiv e label) *
                (source.shadingDensity * ((rho : ENNReal) ^ 2 / 2)) <=
              selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
                quantitativeCarrierFloor Yclean ∧
            (affineJacobian (bucketNormalizedAffineEquiv e label) *
                (source.shadingDensity * ((rho : ENNReal) ^ 2 / 2))) *
                (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
                  (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                      ENNReal) ^ 3) /
                    quantitativeCarrierFloor Yclean))) <=
              selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
                (KT * (certifiedPlankThresholdedAngleScaleCap 576 *
                  ((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                    ENNReal) ^ 3))) := by
  obtain ⟨A, hLoss, hExactOuter, q, hq, hlocalPayment,
      hsurvivingMass, hvolume, hproduct⟩ :=
    exists_selectedOccurrence_exactOuter_survivingDensePayment
      S hrho hrhoHalf P R Y fineBucket hfineBucket hYbucket
        rFrozen hrFrozen
  refine ⟨A, hLoss, hExactOuter, q, hq, ?_⟩
  dsimp only
  let source :=
    (IndexedShadingRefinement.restrictTo Y fineBucket).shading
  let surviving := actualRefinementSurvivingFiberIndices A (some q)
  let B := (blockAt S.activeCoarseFamily P q).fiber
  let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
  refine ⟨hvolume, hproduct, ?_⟩
  have hfinalMass :
      (finalFiberShading A (some q)).shadingMass ≠ 0 := by
    intro hzero
    have hle :=
      Family8ExactAssemblySameDataFiberBridgeV1.ExactAssembly.volume_shadedUnion_le_shadingMass
        (finalFiberShading A (some q))
    rw [hzero] at hle
    exact (not_le_of_gt hvolume) hle
  have hZmass : Z.shadingMass ≠ 0 := by
    rw [← hsurvivingMass,
      actualRefinementSurvivingFiberShading_shadingMass_eq_finalFiberShading]
    exact hfinalMass
  have hsupport : forall p : {p // p ∈ B},
      volume (Z.carrier p) ≠ 0 -> p.1 ∈ surviving := by
    intro p hpVolume
    have hpFiber :
        p.1 ∈ (selectedOccurrenceFactorization P R).index.fiber (some q) := by
      rw [selectedOccurrenceFactorization_fiber P R q hq]
      exact p.2
    have hpFinalVolume :
        volume ((finalFiberShading A (some q)).carrier p.1) ≠ 0 := by
      simpa only [Z, selectedOccurrenceFrozenFinalFiberBlockShading,
        selectedCoarseShading_carrier] using hpVolume
    have hpIndices : p.1 ∈ A.refinement.indices := by
      by_contra hpNot
      apply hpFinalVolume
      rw [finalFiberShading, fiberShading_carrier, if_pos hpFiber,
        A.refinement.carrier_eq_empty_of_not_mem p.1 hpNot, measure_empty]
    apply
      (actualRefinementSurvivingFactorization A).index.mem_fiber
        p.1 (some q) |>.2
    refine ⟨?_, ?_⟩
    · simpa only [actualRefinementSurvivingFactorization_fine] using hpIndices
    · exact
        ((selectedOccurrenceFactorization P R).index.mem_fiber
          p.1 (some q) |>.1 hpFiber).2
  have hcompact :=
    exists_selectedParentArbitraryPlankBucket_positiveCarrier_quantitativeCordoba
      D hD S hrho hrhoOne P q r hr Z hZmass surviving hsupport KT hKT
  dsimp only at hcompact
  obtain ⟨label, hoccupied, ha, hab, hb, hplank, hretained,
      _hcleanMassEq, _hcleanAverageEq, hcleanMass, hcard,
      _hfloorEq, hcordoba⟩ := hcompact
  refine ⟨label, hoccupied, ha, hab, hb, hplank, ?_⟩
  let Yraw := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let Yclean := positiveCarrierShading Yraw
  let hplankPos : forall t,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Yclean t) := fun t =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank t.1.1
  let cert := chosenPlankCertificate hplankPos
  have hlocalPayment' :
      source.shadingDensity *
          ((surviving.card : ENNReal) * ((rho : ENNReal) ^ 2 / 2)) <=
        (frozenComparableLoss (ActiveParentIndex S)
            (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) *
          Z.shadingMass := by
    simpa only [source, surviving, Z] using hlocalPayment
  have hretained' :
      affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          Yclean.shadingMass := by
    simpa only [e, B, Z, Yraw, Yclean] using hretained
  have hcleanMass' : Yclean.shadingMass ≠ 0 := by
    simpa only [e, B, Z, Yraw, Yclean] using hcleanMass
  have hcard' :
      (Fintype.card {t // t ∈ positiveCarrierIndices Yraw} : ENNReal) <=
        (surviving.card : ENNReal) := by
    simpa only [e, B, Z, Yraw, Yclean] using hcard
  have hcross :=
    localCard_sourceDensity_carrierFloorCross_and_thresholdedCordobaCancellation
      (Z := Z) (Yclean := Yclean)
      (sourceDensity := source.shadingDensity)
      (m := (surviving.card : ENNReal))
      (J := affineJacobian (bucketNormalizedAffineEquiv e label))
      (occurrenceLoss :=
        (frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal))
      (bucketLoss :=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal))
      (KT := KT) rho r (sideShapeUpper label 2)
      hcleanMass' hlocalPayment' hretained' hcard'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [e, B, Z, Yraw, Yclean, hplankPos, cert] using hcordoba
  · simpa only [selectedOccurrenceFrozenSameQPositiveCarrierLoss] using
      hcross.1
  · simpa only [selectedOccurrenceFrozenSameQPositiveCarrierLoss] using
      hcross.2

#print axioms selectedOccurrenceFrozenSameQPositiveCarrierLoss
#print axioms
  exists_selectedOccurrence_exactOuter_survivingDense_sameQ_positiveCarrierPayment

end
end Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
