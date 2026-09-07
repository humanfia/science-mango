import Family8Grounding.Family8SelectedParentFineLevelLiftV2
import Family8Grounding.Family8GeneralizedKatzTaoMultiplicityV1

/-!
# Actual fine-level mass retained by a selected-parent plank bucket, V2

Apply the quantitative V9 side-shape selection to the literal fine-level
shading lifted from an `ExactAssembly`.  The weight of a parent is the actual
volume of its shaded piece.  Consequently the total weight is exactly the
mass of `ExactAssembly.sourceFineLevelShading`, and the selected side bucket
retains that mass up to the proved logarithmic loss.

No saturation, angle assignment, container estimate, or multiplicity bound
is stored as an input.  The remaining output is precisely V9's genuine plank
geometry together with an actual filtered mass sum.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFineLevelBucketRetentionV2

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

/-- The actual source fine-level mass survives in one V9 plank bucket up to
the already-proved logarithmic side-shape loss.  The retained sum consists of
literal shaded-piece volumes, not an abstract weight or a desired bound. -/
theorem exists_selectedParentFineLevelPlankBucket_realMassRetention
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
    let parent :=
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let Ylevel :=
      fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S
        (blockAt S.activeCoarseFamily P k).fiber hrho p
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) ∧
      (sourceFineLevelShading A (some k)).shadingMass.toReal <=
        selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ side label,
            shadingPieceRealWeight
              (selectedParentActualShading S Ylevel
                (blockAt S.activeCoarseFamily P k).fiber) p) ∧
      0 < bucketShortA label ∧
      bucketShortA label <= bucketShortB label ∧
      bucketShortB label <= 1 ∧
      forall p, p ∈ sideShapeBucket Finset.univ side label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S
            (blockAt S.activeCoarseFamily P k).fiber p) := by
  dsimp only
  let Ylevel :=
    fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel
  let Zlevel := selectedParentActualShading S Ylevel
    (blockAt S.activeCoarseFamily P k).fiber
  let weight :
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} -> Real :=
    fun p => shadingPieceRealWeight Zlevel p
  have hweightNonneg : forall p, 0 <= weight p := by
    intro p
    dsimp only [weight, shadingPieceRealWeight]
    positivity
  have hbucket :=
    exists_selectedParentActualIsPlankBucket_logarithmicLoss_of_admissible
      D hD S hrho hrhoOne P k r hr weight hweightNonneg
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  refine ⟨label, hoccupied, ?_, ha, hab, hb, hplank⟩
  calc
    (sourceFineLevelShading A (some k)).shadingMass.toReal =
        Zlevel.shadingMass.toReal := by
      apply congrArg ENNReal.toReal
      dsimp only [Zlevel, Ylevel]
      rw [selectedParentFineLevel_shadingMass_eq S D.shading P k A.fineLevel,
        exactAssembly_greedyBlockFineLevelShading_shadingMass S D.shading P k A]
    _ = ∑ p, weight p := by
      exact shadingMass_toReal_eq_sum_shadingPieceRealWeight Zlevel
    _ <= selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p => selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
            shadingPieceRealWeight
              (selectedParentActualShading S Ylevel
                (blockAt S.activeCoarseFamily P k).fiber) p) := by
      exact hretained

#print axioms exists_selectedParentFineLevelPlankBucket_realMassRetention

end

end Family8SelectedParentFineLevelBucketRetentionV2
