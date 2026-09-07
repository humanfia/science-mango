import Family8Grounding.Family8PlankRetainedOwnerActiveCertifiedOwnerIncidenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankActiveSelectedOwnerRepresentativeDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
open Family8CanonicalCertifiedPlankFineAngleRowsV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1
open Family8PlankRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerActiveCertifiedOwnerIncidenceV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# The deduplicated coarse row as an actual shaded family

For every selected owner in the finite `P_{theta,S}` image, choose one active
fine preimage.  Its already-constructed common point makes the restricted
coarse carrier nonempty and transfers every pointwise dense-ball estimate.
The row is also packaged as a literal `ConvexFamily` with its induced shading.
No plank dimensions or volume estimate for the enlarged container are used.
-/

/-- One active fine member representing a deduplicated selected owner. -/
def activeSelectedOwnerRepresentative
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected} :=
  Classical.choose <|
    (mem_activeSelectedOwnersInCertifiedSlab_iff
      D C q cell hcell selected hmass hactive tau S s.1).1 s.2

theorem activeSelectedOwnerRepresentative_mem
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    activeSelectedOwnerRepresentative
        D C q cell hcell selected hmass hactive tau S s ∈
      (activeRetainedOwnerCellCertifiedIncidence
        D C q cell hcell selected hmass hactive).members tau S :=
  (Classical.choose_spec <|
    (mem_activeSelectedOwnersInCertifiedSlab_iff
      D C q cell hcell selected hmass hactive tau S s.1).1 s.2).1

theorem activeSelectedOwnerRepresentative_owner
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    selectedOwnerOfRetained C q
        (activeSelectedOwnerRepresentative
          D C q cell hcell selected hmass hactive tau S s).1 = s.1 :=
  (Classical.choose_spec <|
    (mem_activeSelectedOwnersInCertifiedSlab_iff
      D C q cell hcell selected hmass hactive tau S s.1).1 s.2).2

/-- The actual coarse convex family restricted to the deduplicated row. -/
def activeSelectedOwnerSlabFamily
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    ConvexFamily {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S} :=
  selectedCoarseFamily (retainedOwnerThickenedFamily D C q)
    (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S)

/-- The final cell-restricted induced owner shading, restricted to exactly
the deduplicated row. -/
def activeSelectedOwnerSlabShading
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    Shading (activeSelectedOwnerSlabFamily
      D C q cell hcell selected hmass hactive tau S) :=
  selectedCoarseShading
    (retainedOwnerFinalCoarseShading D C q cell hcell selected)
    (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S)

@[simp] theorem activeSelectedOwnerSlabFamily_apply
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    activeSelectedOwnerSlabFamily
      D C q cell hcell selected hmass hactive tau S s =
        ownerThickenedBody D theta s.1.1 := rfl

@[simp] theorem activeSelectedOwnerSlabShading_carrier
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    (activeSelectedOwnerSlabShading
      D C q cell hcell selected hmass hactive tau S).carrier s =
        (retainedOwnerFinalCoarseShading
          D C q cell hcell selected).carrier s.1 := rfl

/-- The chosen representative's common point lies in the restricted coarse
carrier, so none of the deduplicated coarse carriers is empty. -/
theorem activeSelectedOwnerCommonPoint_mem_coarseCarrier
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    activeCellCommonPoint D C q cell hcell selected
        (activeSelectedOwnerRepresentative
          D C q cell hcell selected hmass hactive tau S s) ∈
      (activeSelectedOwnerSlabShading
        D C q cell hcell selected hmass hactive tau S).carrier s := by
  rw [activeSelectedOwnerSlabShading_carrier,
    ← activeSelectedOwnerRepresentative_owner
      D C q cell hcell selected hmass hactive tau S s]
  exact activeCellCommonPoint_mem_coarse D C q cell hcell selected _

theorem activeSelectedOwnerSlabShading_carrier_nonempty
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    Set.Nonempty ((activeSelectedOwnerSlabShading
      D C q cell hcell selected hmass hactive tau S).carrier s) :=
  ⟨_, activeSelectedOwnerCommonPoint_mem_coarseCarrier
    D C q cell hcell selected hmass hactive tau S s⟩

/-- Any dense-ball estimate on the final coarse union transfers to a literal
point in every deduplicated coarse carrier, with its active fine preimage
recorded at the same time. -/
theorem exists_activeSelectedOwner_commonPoint_denseBall
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) (rho : NNReal) (lower : ENNReal)
    (hball : ∀ x ∈
      (retainedOwnerFinalCoarseShading D C q cell hcell selected).shadedUnion,
        lower ≤ volume
          ((retainedOwnerFinalFineShading D C q cell hcell selected).shadedUnion ∩
            Metric.ball x (rho : Real)))
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    ∃ (i : {i // i ∈ activeRetainedOwnerCellIndices
          D C q cell hcell selected}) (x : Space),
      i ∈ (activeRetainedOwnerCellCertifiedIncidence
        D C q cell hcell selected hmass hactive).members tau S ∧
      selectedOwnerOfRetained C q i.1 = s.1 ∧
      x ∈ (retainedOwnerFinalFineShading
        D C q cell hcell selected).carrier i.1 ∧
      x ∈ (activeSelectedOwnerSlabShading
        D C q cell hcell selected hmass hactive tau S).carrier s ∧
      lower ≤ volume
        ((retainedOwnerFinalFineShading D C q cell hcell selected).shadedUnion ∩
          Metric.ball x (rho : Real)) := by
  let i := activeSelectedOwnerRepresentative
    D C q cell hcell selected hmass hactive tau S s
  let x := activeCellCommonPoint D C q cell hcell selected i
  refine ⟨i, x,
    activeSelectedOwnerRepresentative_mem
      D C q cell hcell selected hmass hactive tau S s,
    activeSelectedOwnerRepresentative_owner
      D C q cell hcell selected hmass hactive tau S s,
    activeCellCommonPoint_mem_fine D C q cell hcell selected i,
    activeSelectedOwnerCommonPoint_mem_coarseCarrier
      D C q cell hcell selected hmass hactive tau S s, ?_⟩
  exact hball x
    (activeCellCommonPoint_mem_coarseShadedUnion
      D C q cell hcell selected i)

/-- The deduplicated coarse row inherits the old V279 angle-occupancy count
through the two explicit finite maps. -/
theorem activeSelectedOwnersInCertifiedSlab_card_le_angleOccupancy
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    {tau : NNReal} {S : ConvexBody Space} (hS : IsSlab 1 tau S) :
    (activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S).card ≤
      canonicalCertifiedFineAngleOccupancy
        (retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
          D C q cell hcell selected hmass) 2 tau := by
  exact (activeSelectedOwnersInCertifiedSlab_card_le_active
    D C q cell hcell selected hmass hactive tau S) |>.trans <|
      (activeCertified_members_card_le_all
        D C q cell hcell selected hmass hactive tau S) |>.trans <|
          retainedOwnerCellRestricted_members_card_le_angleOccupancy
            D C q cell hcell selected hmass hS

/-- Every body of the actual deduplicated coarse family lies in the same
controlled thickening of the queried certified slab. -/
theorem activeSelectedOwnerSlabFamily_subset_sameSlabThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    {tau : NNReal} {S : ConvexBody Space} (hS : IsSlab 1 tau S)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    (activeSelectedOwnerSlabFamily
        D C q cell hcell selected hmass hactive tau S s : Set Space) ⊆
      Metric.cthickening (2 * ((theta * b : NNReal) : Real))
        (S : Set Space) := by
  simpa only [activeSelectedOwnerSlabFamily_apply] using
    activeSelectedOwnerThickenedBody_subset_sameSlabThickening
      D C q cell hcell selected hmass hactive hS s.1 s.2

#print axioms activeSelectedOwnerRepresentative_mem
#print axioms activeSelectedOwnerRepresentative_owner
#print axioms activeSelectedOwnerSlabShading_carrier_nonempty
#print axioms exists_activeSelectedOwner_commonPoint_denseBall
#print axioms activeSelectedOwnersInCertifiedSlab_card_le_angleOccupancy
#print axioms activeSelectedOwnerSlabFamily_subset_sameSlabThickening

end
end Family8PlankActiveSelectedOwnerRepresentativeDatumV1
