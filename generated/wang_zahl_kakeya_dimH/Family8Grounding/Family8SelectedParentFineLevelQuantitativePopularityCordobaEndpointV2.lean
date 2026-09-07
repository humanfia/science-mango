import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV5
import Family8Grounding.Family8SelectedParentQuantitativePopularityCordobaV3

/-!
# Fine-level selected-parent quantitative-popularity Córdoba endpoint, V2

One actual V9 side bucket simultaneously retains the affinely normalized
fine-level mass and obeys the thresholded plank Córdoba estimate after the
automatic half-average popularity restriction.  In the nonzero branch its
floor is bucket mass divided by twice the literal bucket cardinality.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFineLevelQuantitativePopularityCordobaEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentFineLevelBucketRetentionV5
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentQuantitativePopularityCordobaV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Literal cardinality of one actual selected-parent plank bucket. -/
def selectedParentPlankBucketCard
    {fine : UniformTubeFamily delta index}
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) : Nat :=
  (selectedParentPlankBucketIndices e S B hrho label).card

/-- Complete actual fine-level selected-bucket endpoint with an explicit
quantitative popularity floor. -/
theorem exists_selectedParentFineLevelPlankBucket_massRetention_and_quantitativeCordoba
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ylevel :=
      fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    ∃ label : Fin 3 -> Int,
      ∃ hplank : ∀ p : parent,
        p ∈ selectedParentPlankBucketIndices e S B hrho label ->
          IsPlank 576 (bucketShortA label) (bucketShortB label)
            (selectedParentAffineFamily
              (bucketNormalizedAffineEquiv e label) S B p),
        label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
          (fun p => sideShapeLabel (side p)) ∧
        affineJacobian (bucketNormalizedAffineEquiv e label) *
            (sourceFineLevelShading A (some k)).shadingMass ≤
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (selectedParentPlankBucketShading
              e S Ylevel B hrho label).shadingMass ∧
        0 < bucketShortA label ∧
        bucketShortA label ≤ bucketShortB label ∧
        bucketShortB label ≤ 1 ∧
        let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
        (Ybucket.shadingMass = 0 ∨
          quantitativeCarrierFloor Ybucket =
            Ybucket.shadingMass /
              ((selectedParentPlankBucketCard e S B hrho label : ENNReal) * 2)) ∧
        let hplankPos : ∀ q,
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
          selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
        let cert := chosenPlankCertificate hplankPos
        Ybucket.averageMultiplicity ≤
          2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT
              (certifiedPlankThresholdedAngleScaleCap 576 *
                (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                  quantitativeCarrierFloor Ybucket)) := by
  dsimp only
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ :=
    exists_selectedParentFineLevelPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr A
  refine ⟨label, hplank, hoccupied, hretained, ha, hab, hb, ?_, ?_⟩
  · let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ylevel := fineShadingAtGreedyBlockLevel
      S D.shading P k A.fineLevel
    let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
    by_cases hmass : Ybucket.shadingMass = 0
    · exact Or.inl hmass
    · exact Or.inr (by
        simpa only [selectedParentPlankBucketCard, Fintype.card_coe] using
          quantitativeCarrierFloor_eq_mass_div_card_mul_two Ybucket hmass)
  · exact selectedParentPlankBucket_averageMultiplicity_le_quantitativePopularityJohn
      S hrho
        (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
        P k r hr label hplank KT hKT

#print axioms
  exists_selectedParentFineLevelPlankBucket_massRetention_and_quantitativeCordoba

end

end Family8SelectedParentFineLevelQuantitativePopularityCordobaEndpointV2
