import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV2
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQLocalBlockPositiveCarrierPaymentV1
import Family8Grounding.Family8SelectedOccurrenceWeightedWinnerSideBucketV1
import Mathlib.Tactic

/-!
# Winner-side bucket followed by one same-occurrence local payment

This module is the object-level seam between the joint fibre/density bucket
and the loss-aware Proposition 6.6(A) calculation.  It first retains one
mass-weighted winner-side bucket.  The exact frozen assembly and the local
positive-carrier Cordoba bucket are then produced in one call, so neither the
occurrence nor its inner label is reselected.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ActualRefinementSurvivingDenseFiberV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8ExactAssemblySameDataFiberBridgeV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV2
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SameOccurrenceLocalCardCarrierFloorAdapterV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceExactOuterSurvivingDensePaymentV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8SelectedOccurrenceFrozenSameQLocalBlockPositiveCarrierPaymentV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierPaymentV1
open Family8SelectedOccurrenceWeightedWinnerSideBucketV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockPositiveCarrierLocalKTV1
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

/-- The exact payload produced after the winner-side occurrence set has been
fixed.  Its `source` is the literal shading on that set. -/
def WinnerSideLocalBlockPositiveCarrierPaymentPayload
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (rFrozen : Real) (hrho : 0 < rho) (r : NNReal) (hr : 0 < r) : Prop :=
  exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) source rFrozen,
    A.loss = frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) /\
    A.frozenCoarse =
        (selectedOccurrenceFactorization P R).inducedShading
          A.refinement.shading /\
    exists q, q ∈ R /\
      let B := (blockAt S.activeCoarseFamily P q).fiber
      let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
      let d := blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P q)
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
      R.card * B.card <= 2 * Fintype.card (ActiveParentIndex S) /\
      0 < volume (finalFiberShading A (some q)).shadedUnion /\
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A (some q)).averageMultiplicity) /\
      exists label : Fin 3 -> Int,
        label ∈ occupiedWeightBuckets
          (Finset.univ : Finset {p // p ∈ B})
          (fun p => sideShapeLabel
            (selectedParentLongRelabeledSide e S B hrho p)) /\
        0 < bucketShortA label /\
        bucketShortA label <= bucketShortB label /\
        bucketShortB label <= 1 /\
        exists hplank : forall p,
            p ∈ sideShapeBucket Finset.univ
                (fun p => selectedParentLongRelabeledSide e S B
                  hrho p)
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
                (certifiedPlankThresholdedLevels cert) d
                  (certifiedPlankThresholdedAngleScaleCap 576 *
                    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                        ENNReal) ^ 3) /
                      quantitativeCarrierFloor Yclean))) /\
          affineJacobian (bucketNormalizedAffineEquiv e label) *
              (source.shadingDensity * ((rho : ENNReal) ^ 2 / 2)) <=
            selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
              quantitativeCarrierFloor Yclean /\
          (affineJacobian (bucketNormalizedAffineEquiv e label) *
              (source.shadingDensity * ((rho : ENNReal) ^ 2 / 2))) *
              (d * (certifiedPlankThresholdedAngleScaleCap 576 *
                (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                    ENNReal) ^ 3) /
                  quantitativeCarrierFloor Yclean))) <=
            selectedOccurrenceFrozenSameQPositiveCarrierLoss S P *
              (d * (certifiedPlankThresholdedAngleScaleCap 576 *
                ((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                  ENNReal) ^ 3)))

/-- The literal automatic John-side label function on the current occurrence
set.  Naming it prevents repeated reduction through the active-parent datum. -/
noncomputable def winnerSideLabelFunction
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hrho : 0 < rho) :
    Fin (blocks S.activeCoarseFamily P).length -> (Fin 3 -> Int) :=
  fun q => sideShapeLabel
    (winnerLongSide
      (fine := (activeParentActualTubeDatum S D.shading).family) P hrho q)

/-- The retained winner-side occurrence set, as a named literal object. -/
def winnerSideRetainedOccurrences
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hrho : 0 < rho)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (label : Fin 3 -> Int) :
    Finset (Fin (blocks S.activeCoarseFamily P).length) :=
  selectedOccurrenceWinnerSideBucket
    (fine := (activeParentActualTubeDatum S D.shading).family) P hrho R label

/-- The literal source shading before the winner-side restriction. -/
def winnerSideBucketSource
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S)) :
    Shading S.activeCoarseFamily :=
  (IndexedShadingRefinement.restrictTo Y fineBucket).shading

/-- The literal source shading on the retained winner-side occurrence set. -/
def winnerSideRetainedSource
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hrho : 0 < rho)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (label : Fin 3 -> Int) : Shading S.activeCoarseFamily :=
  selectedOccurrenceFineShading
    (fine := (activeParentActualTubeDatum S D.shading).family) P
    (winnerSideRetainedOccurrences D S P hrho R label)
    (winnerSideBucketSource D S Y fineBucket)

/-- The common automatic John-side band on the retained winner-side set. -/
def WinnerSideCommonBand
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hrho : 0 < rho)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (label : Fin 3 -> Int) : Prop :=
  forall q, q ∈ winnerSideRetainedOccurrences D S P hrho R label -> forall j,
    sideShapeUpper label j / 2 <
        winnerLongSide
          (fine := (activeParentActualTubeDatum S D.shading).family) P hrho q j /\
      winnerLongSide
          (fine := (activeParentActualTubeDatum S D.shading).family) P hrho q j <=
        sideShapeUpper label j

/-- The winner-side selection fields, separated from the much larger local
payment payload so each opaque command has its own elaboration budget. -/
def WinnerSideSelectionPayload
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hrho : 0 < rho)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (label : Fin 3 -> Int) : Prop :=
  label ∈ occupiedWeightBuckets R (winnerSideLabelFunction D S P hrho) /\
    (winnerSideRetainedOccurrences D S P hrho R label).Nonempty /\
    winnerSideRetainedOccurrences D S P hrho R label ⊆ R /\
    (winnerSideRetainedSource D S P hrho R Y fineBucket label).shadingMass ≠ 0 /\
    (winnerSideBucketSource D S Y fineBucket).shadingMass <=
      (winnerSideBucketLoss rho : ENNReal) *
        (winnerSideRetainedSource D S P hrho R Y fineBucket label).shadingMass /\
    (winnerSideBucketSource D S Y fineBucket).averageMultiplicity <=
      (winnerSideBucketLoss rho : ENNReal) *
        (winnerSideRetainedSource D S P hrho R Y fineBucket label).averageMultiplicity /\
    WinnerSideCommonBand D S P hrho R label

/-- The complete winner-side output behind a compact opaque head. -/
def WinnerSideLocalBlockPositiveCarrierPaymentConclusion
    (D : ActualTubeDatum delta index) (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (Y : Shading S.activeCoarseFamily)
    (fineBucket : Finset (ActiveParentIndex S))
    (rFrozen : Real) (hrho : 0 < rho) (r : NNReal) (hr : 0 < r) : Prop :=
  exists outerLabel : Fin 3 -> Int,
    WinnerSideSelectionPayload D S P hrho R Y fineBucket outerLabel /\
    WinnerSideLocalBlockPositiveCarrierPaymentPayload D S P
      (winnerSideRetainedOccurrences D S P hrho R outerLabel)
      (winnerSideRetainedSource D S P hrho R Y fineBucket outerLabel)
      rFrozen hrho r hr

/-- Perform the weighted outer-side selection and immediately run the
same-`q` local-block positive-carrier producer on the retained set. -/
theorem exists_winnerSide_sameQ_localBlockPositiveCarrierPayment
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hParent : (activeParentActualTubeDatum S D.shading).IsAdmissible)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
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
    (huniform : forall q, q ∈ R -> forall k, k ∈ R ->
      (((blockAt S.activeCoarseFamily P q).fiber.card : Nat) : ENNReal) <=
        2 * (((blockAt S.activeCoarseFamily P k).fiber.card : Nat) : ENNReal))
    (rFrozen : Real) (hrFrozen : 0 < rFrozen)
    (r : NNReal) (hr : 0 < r) :
    WinnerSideLocalBlockPositiveCarrierPaymentConclusion
      D S P R Y fineBucket rFrozen hrho r hr := by
  classical
  unfold WinnerSideLocalBlockPositiveCarrierPaymentConclusion
  have hfineContained : forall i : ActiveParentIndex S, i ∈ Finset.univ ->
      ((activeParentActualTubeDatum S D.shading).family.tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
    intro i _hi
    exact hParent.contained_in_unit_ball i
  obtain ⟨outerLabel, houterLabel, hRsideNonempty, hRsideSubset,
      hYside0, hmass, havg, hsides⟩ :=
    exists_selectedOccurrence_weightedWinnerSideBucket
      (fine := (activeParentActualTubeDatum S D.shading).family)
      (P := P) hrho hfineContained R Y fineBucket hfineBucket hYbucket
  refine ⟨outerLabel, ?_, ?_⟩
  · unfold WinnerSideSelectionPayload WinnerSideCommonBand
    simp only [winnerSideRetainedOccurrences, winnerSideBucketSource,
      winnerSideRetainedSource]
    exact ⟨houterLabel, hRsideNonempty, hRsideSubset, hYside0,
      hmass, havg, hsides⟩
  · let Rside := winnerSideRetainedOccurrences D S P hrho R outerLabel
    let Ybucket := winnerSideBucketSource D S Y fineBucket
    have hlocal :=
      exists_selectedOccurrence_exactOuter_survivingDense_sameQ_localBlockPositiveCarrierPayment
      D hD S hrho hrhoOne hrhoHalf P Rside Ybucket
        (selectedOccurrenceFineIndices P Rside)
        (by exact fun _ hi => hi) (by
          change (selectedOccurrenceFineShading
            (fine := (activeParentActualTubeDatum S D.shading).family)
            P Rside Ybucket).shadingMass ≠ 0
          exact hYside0)
        (fun q _hq => selectedParentBlock_isFrostmanIn_one S D.shading P q)
        (fun q hq k hk =>
          huniform q (hRsideSubset hq) k (hRsideSubset hk))
        rFrozen hrFrozen r hr
    change WinnerSideLocalBlockPositiveCarrierPaymentPayload D S P Rside
      (selectedOccurrenceFineShading
        (fine := (activeParentActualTubeDatum S D.shading).family)
        P Rside Ybucket)
      rFrozen hrho r hr
    exact hlocal

#print axioms exists_winnerSide_sameQ_localBlockPositiveCarrierPayment

end

end Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
