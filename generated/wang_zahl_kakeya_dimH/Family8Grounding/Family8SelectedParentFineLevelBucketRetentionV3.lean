import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV2

/-!
# Package actual fine-level bucket retention as a shading mass, V3

The V2 theorem retains a filtered sum of literal shaded-piece volumes.  This
module identifies that sum with the shading mass of an honest pre-affine
bucket restriction.  Thus downstream arguments consume an actual `Shading`
object rather than reopening the finite weighted sum.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFineLevelBucketRetentionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentFineLevelBucketRetentionV2
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
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
set_option maxHeartbeats 4000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal selected bucket before the common affine normalization. -/
def selectedParentPreAffinePlankBucketShading
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) :
    Shading (selectedCoarseFamily
      (selectedCoarseFamily S.activeCoarseFamily B)
      (selectedParentPlankBucketIndices e S B hrho label)) :=
  selectedCoarseShading (selectedParentActualShading S Y B)
    (selectedParentPlankBucketIndices e S B hrho label)

/-- The real mass of the literal pre-affine bucket is exactly the filtered
sum of the corresponding parent shaded-piece weights. -/
theorem selectedParentPreAffinePlankBucketShading_mass_toReal
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) :
    (selectedParentPreAffinePlankBucketShading
      e S Y B hrho label).shadingMass.toReal =
      ∑ p ∈ selectedParentPlankBucketIndices e S B hrho label,
        shadingPieceRealWeight (selectedParentActualShading S Y B) p := by
  rw [shadingMass_toReal_eq_sum_shadingPieceRealWeight]
  rw [← Finset.attach_eq_univ]
  calc
    (∑ p ∈ (selectedParentPlankBucketIndices e S B hrho label).attach,
        shadingPieceRealWeight
          (selectedParentPreAffinePlankBucketShading e S Y B hrho label) p) =
        ∑ p ∈ (selectedParentPlankBucketIndices e S B hrho label).attach,
          shadingPieceRealWeight (selectedParentActualShading S Y B) p.1 := by
      rfl
    _ = ∑ p ∈ selectedParentPlankBucketIndices e S B hrho label,
          shadingPieceRealWeight (selectedParentActualShading S Y B) p :=
      Finset.sum_attach _ _

/-- V2's filtered-volume retention, now stated entirely through the genuine
pre-affine bucket shading mass. -/
theorem exists_selectedParentFineLevelPlankBucket_shadingMassRetention
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ylevel :=
      fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) ∧
      (sourceFineLevelShading A (some k)).shadingMass.toReal <=
        selectedParentLogarithmicSideBucketLoss rho *
          (selectedParentPreAffinePlankBucketShading
            e S Ylevel B hrho label).shadingMass.toReal ∧
      0 < bucketShortA label ∧
      bucketShortA label <= bucketShortB label ∧
      bucketShortB label <= 1 ∧
      forall p, p ∈ sideShapeBucket Finset.univ side label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S B p) := by
  dsimp only
  have hbucket :=
    exists_selectedParentFineLevelPlankBucket_realMassRetention
      D hD S hrho hrhoOne P k r hr A
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  refine ⟨label, hoccupied, ?_, ha, hab, hb, hplank⟩
  calc
    (sourceFineLevelShading A (some k)).shadingMass.toReal <=
        selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p => selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
            shadingPieceRealWeight
              (selectedParentActualShading S
                (fineShadingAtGreedyBlockLevel
                  S D.shading P k A.fineLevel)
                (blockAt S.activeCoarseFamily P k).fiber) p) := hretained
    _ = selectedParentLogarithmicSideBucketLoss rho *
          (selectedParentPreAffinePlankBucketShading
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S
            (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
            (blockAt S.activeCoarseFamily P k).fiber hrho label).shadingMass.toReal := by
      rw [selectedParentPreAffinePlankBucketShading_mass_toReal]
      rfl

#print axioms selectedParentPreAffinePlankBucketShading_mass_toReal
#print axioms exists_selectedParentFineLevelPlankBucket_shadingMassRetention

end

end Family8SelectedParentFineLevelBucketRetentionV3
