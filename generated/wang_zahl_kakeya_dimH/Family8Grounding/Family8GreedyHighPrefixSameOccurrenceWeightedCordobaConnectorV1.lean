import Family8Grounding.Family8GreedyHighPrefixSameOccurrenceWeightedMassV1
import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import Family8Grounding.Family8SelectedParentArbitraryBlockQuantitativeCordobaV2

/-!
# Same-occurrence weighted high prefix to quantitative Cordoba

The high-prefix weighted selector chooses one actually occupied high greedy
occurrence `q` and represents its retained selected indices by a shading on
the whole literal `q`-block, with zero carriers outside the retained bucket.
The arbitrary-block Cordoba endpoint accepts exactly that shading.

This connector keeps the same dependent `q`, the same literal block, and the
same zero-extended shading throughout.  Its visible loss is the product of

* the pre-existing source-to-selected loss,
* the exact number of occupied high-occurrence labels, and
* the unchanged quantitative Cordoba loss.

It does not use the redundant average-multiplicity output of the high-prefix
dichotomy and never replaces the retained shading by the full block shading.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyHighPrefixSameOccurrenceWeightedCordobaConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8GreedyHighPrefixSameOccurrenceWeightedMassV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
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

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The occupied same-`q` high-prefix shading feeds directly into the
arbitrary-block Cordoba theorem.  The source average is bounded with the
explicit product `firstLoss * Q.card` times the theorem's unchanged
side-bucket and certified-plank losses. -/
theorem exists_sameOccurrenceWeightedCordoba_of_highPrefix
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (Y : Shading D.family.bodyFamily)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (A : ENNReal) (selected : Finset (ActiveParentIndex S))
    (hselected : selected.Nonempty)
    (hcover : ∀ i ∈ selected,
      ∃ q : Fin (blocks S.activeCoarseFamily P).length,
        i ∈ (blockAt S.activeCoarseFamily P q).fiber ∧
        ActualHighConcentrationOccurrence
          (activeParentActualTubeDatum S Y) P A q)
    (firstLoss : ENNReal)
    (hfirst : (activeParentActualTubeDatum S Y).shading.shadingMass <=
      firstLoss *
        (restrictActualTubeDatum
          (activeParentActualTubeDatum S Y) selected).shading.shadingMass)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    ∃ q : CertifiedHighOccurrenceLabel
        (activeParentActualTubeDatum S Y) P A,
      q ∈ occupiedCertifiedHighOccurrences
        (activeParentActualTubeDatum S Y) P A selected hcover ∧
      let B := (blockAt S.activeCoarseFamily P q.1).fiber
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P q.1) r hr
      let parent := {p // p ∈ B}
      let side : parent -> Fin 3 -> NNReal := fun p =>
        selectedParentLongRelabeledSide e S B hrho p
      let Z := sameOccurrenceBlockShading
        (activeParentActualTubeDatum S Y) P A selected hcover q
      ∃ label : Fin 3 -> Int,
        label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
          (fun p => sideShapeLabel (side p)) ∧
        0 < bucketShortA label ∧
        bucketShortA label <= bucketShortB label ∧
        bucketShortB label <= 1 ∧
        ∃ hplank : ∀ p,
            p ∈ sideShapeBucket Finset.univ side label ->
              IsPlank 576 (bucketShortA label) (bucketShortB label)
                (selectedParentAffineFamily
                  (bucketNormalizedAffineEquiv e label) S B p),
          let Ybucket := selectedParentArbitraryPlankBucketShading
            e S B hrho label Z
          let hplankPos : ∀ t,
              IsPlank 576 (bucketShortA label) (bucketShortB label)
                (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
            selectedParentPlankBucket_isPlank
              e S B hrho label hplank t.1
          let cert := chosenPlankCertificate hplankPos
          (activeParentActualTubeDatum S Y).shading.averageMultiplicity <=
            (firstLoss *
              ((occupiedCertifiedHighOccurrences
                (activeParentActualTubeDatum S Y)
                P A selected hcover).card : ENNReal)) *
              ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
                (2 * certifiedPlankDyadicFactor
                  (certifiedPlankThresholdedLevels cert) KT
                    (certifiedPlankThresholdedAngleScaleCap 576 *
                      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                        quantitativeCarrierFloor Ybucket)))) := by
  dsimp only
  let parentD := activeParentActualTubeDatum S Y
  let Q := occupiedCertifiedHighOccurrences parentD P A selected hcover
  have hselection :=
    exists_sameOccurrenceBlockShading_weighted_retention
      parentD P A selected hselected hcover firstLoss hfirst
  obtain ⟨q, hq, _hselectedMass, _hsourceMass, hsourceAverage⟩ := hselection
  let Z := sameOccurrenceBlockShading parentD P A selected hcover q
  have hcordoba :=
    exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le
      D hD S hrho hrhoOne P q.1 r hr Z KT hKT
  dsimp only at hcordoba
  obtain ⟨label, hoccupied, ha, hab, hb, hplank, hbound⟩ := hcordoba
  refine ⟨q, ?_, label, hoccupied, ha, hab, hb, hplank, ?_⟩
  · simpa only [Q, parentD] using hq
  · exact hsourceAverage.trans (mul_le_mul' le_rfl hbound)

#print axioms exists_sameOccurrenceWeightedCordoba_of_highPrefix

end
end Family8GreedyHighPrefixSameOccurrenceWeightedCordobaConnectorV1
