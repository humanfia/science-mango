import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerSameScaleLinearCountV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankHeavyActiveSelectedOwnerRowMassEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8CanonicalCertifiedPlankFineAngleRowsV1
open Family8PlankHeavyRetainedOwnerCellRestrictedCanonicalSlabV1
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankHeavyActiveSelectedOwnerRepresentativeDatumV2
open Family8PlankHeavyActiveSelectedOwnerFlatPrismCountV1
open Family8PlankHeavyActiveSelectedOwnerSameScaleLinearCountV2

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Rowwise mass endpoint on the actual heavy certified owner row

The heavy restriction was performed before CubeWeight and slab selection.
Consequently every owner appearing in a final active certified row is
definitionally a member of `heavyRetainedOwners`, so its original complete
owner fibre carries the common half-average mass floor.  The same owner also
has the already proved carrier comparison and controlled slab containment.
-/

/-- The missing rowwise owner-fibre mass lower bound on every literal final
active owner. -/
theorem activeSelectedOwner_halfAverageFloor_le_ownerFiberMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s.1.1 :=
  heavyRetainedOwner_row_mass_floor C q s.1

/-- The three same-object facts needed by the retained-owner consumer for one
active row: complete-fibre mass floor, restricted carrier comparison, and the
controlled certified slab container. -/
def HeavyActiveSelectedOwnerRowEndpoint
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    (thetaScale : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive thetaScale S}) : Prop :=
  retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s.1.1 ∧
  volume ((activeSelectedOwnerSlabShading
    D C q cell hcell selected hmass hactive thetaScale S).carrier s) ≤
      ownerFiberMass C s.1.1 ∧
  (ownerThickenedBody D theta s.1.1 : Set Space) ⊆
    Metric.cthickening (2 * ((theta * b : NNReal) : Real)) (S : Set Space)

theorem heavyActiveSelectedOwnerRowEndpoint
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    {S : ConvexBody Space} (hS : IsSlab 1 theta S)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive theta S}) :
    HeavyActiveSelectedOwnerRowEndpoint
      D C q cell hcell selected hmass hactive theta S s := by
  refine ⟨
    activeSelectedOwner_halfAverageFloor_le_ownerFiberMass
      D C q cell hcell selected hmass hactive theta S s,
    activeSelectedOwner_carrier_volume_le_ownerFiberMass
      D C q cell hcell selected hmass hactive theta S s,
    ?_⟩
  exact activeSelectedOwnerThickenedBody_subset_sameSlabThickening
    D C q cell hcell selected hmass hactive hS s.1 s.2

/-- The final certified row simultaneously has the geometric count bound and
the rowwise mass lower bound; both statements concern exactly the same heavy
owner finset. -/
theorem activeSelectedOwners_count_and_rowMassFloor
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selected).Nonempty)
    {S : ConvexBody Space} (hS : IsSlab 1 theta S) :
    ((activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive theta S).card : ENNReal) ≤
      min
        (canonicalCertifiedFineAngleOccupancy
          (heavyRetainedOwnerCellRestrictedCanonicalUnitSlabIncidence
            D C q cell hcell selected hmass) 2 theta : ENNReal)
        ((maximalConcentration D.family * (125 * (theta : ENNReal))) /
          (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
            ((a : ENNReal) * (b : ENNReal)))) ∧
    ∀ s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive theta S},
      retainedOwnerHalfAverageFloor C q ≤ ownerFiberMass C s.1.1 := by
  refine ⟨
    activeSelectedOwners_card_le_min_angleOccupancy_linearReserve
      D C q cell hcell selected hmass hactive hS,
    ?_⟩
  intro s
  exact activeSelectedOwner_halfAverageFloor_le_ownerFiberMass
    D C q cell hcell selected hmass hactive theta S s

#print axioms activeSelectedOwner_halfAverageFloor_le_ownerFiberMass
#print axioms HeavyActiveSelectedOwnerRowEndpoint
#print axioms heavyActiveSelectedOwnerRowEndpoint
#print axioms activeSelectedOwners_count_and_rowMassFloor

end
end Family8PlankHeavyActiveSelectedOwnerRowMassEndpointV2
