import Family8Grounding.Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
import Family8Grounding.Family8SelectedParentFrozenComparablePlankBucketV3

/-!
# Frozen comparable assembly with an automatic quantitative Cordoba fibre

Apply the automatic arbitrary-block Cordoba theorem to the same surviving
fibre selected by the collision-free frozen comparable assembly.  The output
contains the genuine fibre estimate and its insertion into the frozen
outer-times-fibre average-product estimate.  No angle assignment, convex
container, scale inequality, carrier floor, or multiplicity conclusion is an
input.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFrozenComparableQuantitativeCordobaV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentFrozenComparablePlankBucketV3
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
set_option maxHeartbeats 10000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- A polylogarithmic frozen assembly has a surviving fibre whose actual V9
plank bucket satisfies the fully automatic quantitative Cordoba bound. -/
theorem exists_frozenComparable_selectedParentQuantitativeCordoba
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r)
    (rFrozen : Real) (hrFrozen : 0 < rFrozen)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (greedyParentFactorization S P)
        (parentAggregatedShading S D.shading) rFrozen,
      A.loss = frozenComparableLoss (ActiveParentIndex S)
        (Option (Fin (blocks S.activeCoarseFamily P).length)) ∧
      ∃ k : Fin (blocks S.activeCoarseFamily P).length,
        let B := (blockAt S.activeCoarseFamily P k).fiber
        let Z := frozenFinalGreedyBlockShading D S P A k
        let e := contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
        let parent := {p // p ∈ B}
        let side : parent -> Fin 3 -> NNReal := fun p =>
          selectedParentLongRelabeledSide e S B hrho p
        0 < volume Z.shadedUnion ∧
        ∃ label : Fin 3 -> Int,
          label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
            (fun p => sideShapeLabel (side p)) ∧
          0 < bucketShortA label ∧
          bucketShortA label <= bucketShortB label ∧
          bucketShortB label <= 1 ∧
          ∃ hplank : forall p,
              p ∈ sideShapeBucket Finset.univ side label ->
                IsPlank 576 (bucketShortA label) (bucketShortB label)
                  (selectedParentAffineFamily
                    (bucketNormalizedAffineEquiv e label) S B p),
            let Ybucket := selectedParentArbitraryPlankBucketShading
              e S B hrho label Z
            let hplankPos : forall q,
                IsPlank 576 (bucketShortA label) (bucketShortB label)
                  (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
              selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
            let cert := chosenPlankCertificate hplankPos
            let cordobaFactor := 2 * certifiedPlankDyadicFactor
              (certifiedPlankThresholdedLevels cert) KT
                (certifiedPlankThresholdedAngleScaleCap 576 *
                  (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                    quantitativeCarrierFloor Ybucket))
            Z.averageMultiplicity <=
                (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
                  cordobaFactor ∧
              (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
                A).averageMultiplicity <=
                4 * (A.frozenCoarse.averageMultiplicity *
                  ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
                    cordobaFactor)) := by
  obtain ⟨A, hLoss, k, hZVolume, hproduct, _hbucket⟩ :=
    exists_frozenComparable_selectedParentPlankBucket
      D hD S hrho hrhoOne P r hr rFrozen hrFrozen hsource
  let Z := frozenFinalGreedyBlockShading D S P A k
  have hcordoba :=
    exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le
      D hD S hrho hrhoOne P k r hr Z KT hKT
  dsimp only at hcordoba
  obtain ⟨label, hoccupied, ha, hab, hb, hplank, hZcordoba⟩ := hcordoba
  refine ⟨A, hLoss, k, hZVolume, label, hoccupied, ha, hab, hb,
    hplank, hZcordoba, ?_⟩
  exact hproduct.trans
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hZcordoba))

#print axioms exists_frozenComparable_selectedParentQuantitativeCordoba

end

end Family8SelectedParentFrozenComparableQuantitativeCordobaV5
