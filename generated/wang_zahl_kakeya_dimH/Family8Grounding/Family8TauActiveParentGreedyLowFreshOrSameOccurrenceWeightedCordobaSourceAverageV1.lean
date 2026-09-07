import Family8Grounding.Family8NormalizedLongCoreFirstOuterParentTransportV2
import Family8Grounding.Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaV1

/-!
# Source-average lift of the tau-active low/high Cordoba split

The full-refinement first-outer transport compares the original datum's
average multiplicity with the literal source-to-tau parent aggregation.  The
tau-active greedy theorem uses definitionally that same parent shading.  This
file composes the two without reselecting a greedy partition, high prefix,
occurrence label, block, or shading.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaSourceAverageV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8GreedyHighPrefixSameOccurrenceWeightedMassV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreFirstOuterParentTransportV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-- Both branches of the tau-active split are lifted to the original source
average using the exact doubled-fibre Katz--Tao first factor.  The high branch
keeps every dependent same-occurrence witness unchanged. -/
theorem exists_source_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba
    {betaKT epsilonKT etaKT : Real} {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters betaKT epsilonKT etaKT delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C L.N L.epsilon L.eta S)
    (A : ENNReal)
    (htauHalf : S.tau W.m <= (2 : NNReal)⁻¹)
    (hgeometry : TauActiveCoarseAdmissibility
      (fullRefinementDatum D) C S W)
    (hdelta0 : S.tau W.m / 8 <= delta0)
    (hdensityBudget :
      (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).shading.shadingDensity)
    (hcoefficient :
      128 * A <=
        ((S.tau W.m / 8 : NNReal) : ENNReal) ^ (-etaKT))
    {sourceEtaKT : Real} (hSourceKT : KatzTaoHypotheses D sourceEtaKT)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover (fullRefinementDatum D) C S W).activeCoarseFamily) :
    let firstCap : ENNReal :=
      Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT))
    (exists selectedLow : Finset
          {k // k ∈ (tauScaleCover
            (fullRefinementDatum D) C S W).activeCoarse},
        exists selectedFresh : Finset {k // k ∈ selectedLow},
          selectedFresh.Nonempty /\
          selectedFresh.card <= selectedLow.card /\
          D.shading.averageMultiplicity <=
            firstCap *
              ((2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
                katzTaoMultiplicityRHS
                  (S.tau W.m / 8) selectedFresh.card epsilonKT betaKT)) \/
      exists G : GreedyDensityPartition
          (activeParentActualTubeDatum
            (tauScaleCover (fullRefinementDatum D) C S W)
            (fullRefinementDatum D).shading).family.bodyFamily
          (hullCandidates (Finset.univ : Finset
            {k // k ∈ (tauScaleCover
              (fullRefinementDatum D) C S W).activeCoarse}))
          (hullContainer
            (activeParentActualTubeDatum
              (tauScaleCover (fullRefinementDatum D) C S W)
              (fullRefinementDatum D).shading).family.bodyFamily)
          Finset.univ,
        exists selected : Finset
            {k // k ∈ (tauScaleCover
              (fullRefinementDatum D) C S W).activeCoarse},
          exists hcover : (forall k, k ∈ selected ->
            exists q : Fin (blocks
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading).family.bodyFamily G).length,
              k ∈ (blockAt
                (activeParentActualTubeDatum
                  (tauScaleCover (fullRefinementDatum D) C S W)
                  (fullRefinementDatum D).shading).family.bodyFamily
                G q).fiber /\
              ActualHighConcentrationOccurrence
                (activeParentActualTubeDatum
                  (tauScaleCover (fullRefinementDatum D) C S W)
                  (fullRefinementDatum D).shading)
                G A q),
          exists q : CertifiedHighOccurrenceLabel
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading) G A,
            q ∈ occupiedCertifiedHighOccurrences
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading)
              G A selected hcover /\
            let B := (blockAt
              (tauScaleCover (fullRefinementDatum D) C S W).activeCoarseFamily
              G q.1).fiber
            let e := contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover (fullRefinementDatum D) C S W)
                (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m))
                G q.1) r hr
            let parent := {p // p ∈ B}
            let side : parent -> Fin 3 -> NNReal := fun p =>
              selectedParentLongRelabeledSide e
                (tauScaleCover (fullRefinementDatum D) C S W) B
                (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m)) p
            let Z := sameOccurrenceBlockShading
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading)
              G A selected hcover q
            exists label : Fin 3 -> Int,
              label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
                (fun p => sideShapeLabel (side p)) /\
              0 < bucketShortA label /\
              bucketShortA label <= bucketShortB label /\
              bucketShortB label <= 1 /\
              exists hplank : forall p,
                  p ∈ sideShapeBucket Finset.univ side label ->
                    IsPlank 576 (bucketShortA label) (bucketShortB label)
                      (selectedParentAffineFamily
                        (bucketNormalizedAffineEquiv e label)
                        (tauScaleCover (fullRefinementDatum D) C S W) B p),
                let Ybucket := selectedParentArbitraryPlankBucketShading
                  e (tauScaleCover (fullRefinementDatum D) C S W) B
                  (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m))
                  label Z
                let hplankPos : forall t,
                    IsPlank 576 (bucketShortA label) (bucketShortB label)
                      (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
                  selectedParentPlankBucket_isPlank
                    e (tauScaleCover (fullRefinementDatum D) C S W) B
                    (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m))
                    label hplank t.1
                let cert := chosenPlankCertificate hplankPos
                D.shading.averageMultiplicity <=
                  firstCap *
                    ((2 *
                      ((occupiedCertifiedHighOccurrences
                        (activeParentActualTubeDatum
                          (tauScaleCover (fullRefinementDatum D) C S W)
                          (fullRefinementDatum D).shading)
                        G A selected hcover).card : ENNReal)) *
                      ((selectedParentLogarithmicSideBucketLoss
                          (S.tau W.m) : ENNReal) *
                        (2 * certifiedPlankDyadicFactor
                          (certifiedPlankThresholdedLevels cert) KT
                            (certifiedPlankThresholdedAngleScaleCap 576 *
                              (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                                  ENNReal) ^ 3) /
                                quantitativeCarrierFloor Ybucket))))) := by
  dsimp only
  have hfirst : D.shading.averageMultiplicity <=
      (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT)) : ENNReal) *
        (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).shading.averageMultiplicity := by
    change D.shading.averageMultiplicity <=
      (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT)) : ENNReal) *
        (parentAggregatedShading
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).averageMultiplicity
    rw [← show sourceTauCover (fullRefinementDatum D) C S W.m =
      tauScaleCover (fullRefinementDatum D) C S W from rfl]
    exact
      Family8NormalizedLongCoreFirstOuterParentTransportV2.NormalizedLongIntervalCoreWitness.fullRefinement_averageMultiplicity_le_firstCap_mul_sourceTauParent
        D hD C S L W hSourceKT
  have hsplit :=
    exists_tauActiveParent_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba
      hKTP (fullRefinementDatum D) hD.delta_pos C S W A htauHalf hgeometry
        hdelta0 hdensityBudget hcoefficient r hr KT hKT
  rcases hsplit with hlow | hhigh
  · left
    obtain ⟨selectedLow, selectedFresh, hnonempty, hcard, hbound⟩ := hlow
    refine ⟨selectedLow, selectedFresh, hnonempty, hcard, ?_⟩
    exact hfirst.trans (mul_le_mul' le_rfl hbound)
  · right
    obtain ⟨G, selected, hcover, q, hq, label, hoccupied, ha, hab, hb,
      hplank, hbound⟩ := hhigh
    refine ⟨G, selected, hcover, q, hq, label, hoccupied, ha, hab, hb,
      hplank, ?_⟩
    exact hfirst.trans (mul_le_mul' le_rfl hbound)

#print axioms
  exists_source_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba

end
end Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaSourceAverageV1
