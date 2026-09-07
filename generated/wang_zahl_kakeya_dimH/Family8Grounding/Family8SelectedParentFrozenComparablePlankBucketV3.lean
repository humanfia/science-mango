import Family8Grounding.Family8SelectedParentArbitraryBlockPlankBucketV4
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1

/-!
# A polylogarithmic frozen surviving fibre in an actual V9 plank bucket

Apply the collision-free frozen comparable assembly to the occurrence-indexed
greedy factorization of the active parent family.  Its positive surviving
fibre is necessarily one literal greedy block.  Reindex that same shading on
the block subtype and feed it to the arbitrary-shading V9 bucket bridge.

Thus the selected plank bucket is attached to the same actual fibre appearing
in the frozen outer/fibre average-product bound.  No coarse-card averaging or
`P.length` loss is introduced; the only selection losses are the constructed
frozen polylogarithmic loss and the constructed logarithmic side-shape loss.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFrozenComparablePlankBucketV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8FrozenComparableActualAverageMassDensityV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The actual frozen final fibre, reindexed by its literal greedy-block
subtype. -/
def frozenFinalGreedyBlockShading
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) rFrozen)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber) :=
  selectedCoarseShading
    (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
      A (some k))
    (blockAt S.activeCoarseFamily P k).fiber

/-- Carrier equality between the subtype representative and the ambient
frozen final-fibre shading. -/
theorem frozenFinalGreedyBlockShading_carrier
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) rFrozen)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}) :
    (frozenFinalGreedyBlockShading D S P A k).carrier p =
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
        A (some k)).carrier p.1 := by
  rw [frozenFinalGreedyBlockShading]
  rfl

/-- Reindexing the frozen fibre preserves its multiplicity-counted mass. -/
theorem frozenFinalGreedyBlockShading_shadingMass
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) rFrozen)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    (frozenFinalGreedyBlockShading D S P A k).shadingMass =
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
        A (some k)).shadingMass := by
  rw [frozenFinalGreedyBlockShading, selectedCoarseShading_mass]
  rw [Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading,
    fiberShading_mass_eq_sum_fiber,
    greedyParentFactorization_fiber_eq_block S P k]
  apply Finset.sum_congr rfl
  intro p hp
  rw [fiberShading_carrier, if_pos]
  rw [greedyParentFactorization_fiber_eq_block S P k]
  exact hp

/-- Reindexing also preserves the genuine shaded union. -/
theorem frozenFinalGreedyBlockShading_shadedUnion
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) rFrozen)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    (frozenFinalGreedyBlockShading D S P A k).shadedUnion =
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
        A (some k)).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr
      ⟨p.1, by
        rw [← frozenFinalGreedyBlockShading_carrier D S P A k p]
        exact hxp⟩
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    rw [Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading,
      fiberShading_carrier] at hxp
    by_cases hp : p ∈ (greedyParentFactorization S P).index.fiber (some k)
    · rw [if_pos hp] at hxp
      have hpBlock : p ∈ (blockAt S.activeCoarseFamily P k).fiber := by
        rw [← greedyParentFactorization_fiber_eq_block S P k]
        exact hp
      let pp : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} :=
        ⟨p, hpBlock⟩
      exact Set.mem_iUnion.mpr
        ⟨pp, by
          change x ∈
            (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
              A (some k)).carrier pp.1
          rw [Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading,
            fiberShading_carrier, if_pos hp]
          exact hxp⟩
    · rw [if_neg hp] at hxp
      exact hxp.elim

/-- Hence the actual average multiplicity of the same frozen fibre is
unchanged. -/
theorem frozenFinalGreedyBlockShading_averageMultiplicity
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) rFrozen)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    (frozenFinalGreedyBlockShading D S P A k).averageMultiplicity =
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
        A (some k)).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [frozenFinalGreedyBlockShading_shadingMass D S P A k,
    frozenFinalGreedyBlockShading_shadedUnion D S P A k]

/-- Canonical paper-facing connector: construct the polylogarithmic frozen
assembly, choose its genuinely positive surviving greedy block, and produce a
logarithmically retained actual affine plank bucket on that very same fibre. -/
theorem exists_frozenComparable_selectedParentPlankBucket
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
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0) :
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
        (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
          A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity * Z.averageMultiplicity) ∧
        ∃ label : Fin 3 -> Int,
          label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
            (fun p => sideShapeLabel (side p)) ∧
          affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              (selectedParentArbitraryPlankBucketShading
                e S B hrho label Z).shadingMass ∧
          0 < bucketShortA label ∧
          bucketShortA label <= bucketShortB label ∧
          bucketShortB label <= 1 ∧
          forall p, p ∈ sideShapeBucket Finset.univ side label ->
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (selectedParentAffineFamily
                (bucketNormalizedAffineEquiv e label) S B p) := by
  obtain ⟨A, hLoss, _hFiberLabel, _hOuterLabel, _hmass, _hdensity,
      q, hq, hqVolume, _hfiberLower, _hfiberUpper,
      _houterLower, _houterUpper, hproduct⟩ :=
    exists_frozenComparableAssembly_with_actualAverages_mass_density
      (greedyParentFactorization S P) (parentAggregatedShading S D.shading)
      rFrozen hrFrozen hsource
  change q ∈ (indexFactorization S.activeCoarseFamily P).coarse at hq
  rw [indexFactorization_coarse, occurrenceIndices] at hq
  obtain ⟨k, _hk, hq⟩ := Finset.mem_image.mp hq
  subst q
  let Z := frozenFinalGreedyBlockShading D S P A k
  have hZVolume : 0 < volume Z.shadedUnion := by
    rw [frozenFinalGreedyBlockShading_shadedUnion D S P A k]
    exact hqVolume
  have hproductZ :
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
        A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity * Z.averageMultiplicity) := by
    rw [frozenFinalGreedyBlockShading_averageMultiplicity D S P A k]
    exact hproduct
  have hbucket :=
    exists_selectedParentArbitraryPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr Z
  dsimp only at hbucket
  exact ⟨A, hLoss, k, hZVolume, hproductZ, hbucket⟩

#print axioms frozenFinalGreedyBlockShading_carrier
#print axioms frozenFinalGreedyBlockShading_shadingMass
#print axioms frozenFinalGreedyBlockShading_shadedUnion
#print axioms frozenFinalGreedyBlockShading_averageMultiplicity
#print axioms exists_frozenComparable_selectedParentPlankBucket

end

end Family8SelectedParentFrozenComparablePlankBucketV3
