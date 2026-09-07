import Family8Grounding.Family8CanonicalCertifiedPlankFineAngleRowsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankRetainedOwnerActiveCellCommonBallContainerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalCertifiedPlankSlabIncidenceCoreV3
open Family8PlankThickControlActualClusterV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Active support and controlled owner containers for the retained cell datum

Cell restriction changes the shading but not the fine index type.  Thus the
canonical incidence from V279 may still contain fine planks whose restricted
shading is empty.  The dense-ball theorem cannot be applied to such an index.

This file makes the required support pruning literal.  Every surviving fine
index has a chosen point which belongs simultaneously to its restricted fine
shading and to the restricted shading of its constructed thickened owner.
Consequently any pointwise dense-ball estimate on the latter applies at the
same point.  Independently, mutual thickening puts the owner body inside the
double-radius closed thickening of the fine body, and hence inside the same
controlled thickening of every certified slab containing that fine body.
-/

def retainedOwnerFinalFineShading
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    Shading (retainedOwnerPlankFamily D C q).family :=
  restrictToCells (retainedOwnerPlankFamily D C q).shading
    cell hcell selected

def retainedOwnerFinalCoarseShading
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    Shading (retainedOwnerThickenedFamily D C q) :=
  restrictToCells (retainedOwnerThickenedShading D C q)
    cell hcell selected

/-- Exactly the fine indices left with nonempty shading after the common cell
restriction.  This is the support on which a dense-ball point can honestly be
chosen. -/
def activeRetainedOwnerCellIndices
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex) :
    Finset {i // i ∈ retainedOwnerSourceIndices C q} := by
  classical
  exact Finset.univ.filter fun i ↦
    Set.Nonempty
      ((retainedOwnerFinalFineShading D C q cell hcell selected).carrier i)

@[simp] theorem mem_activeRetainedOwnerCellIndices
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ retainedOwnerSourceIndices C q}) :
    i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected ↔
      Set.Nonempty
        ((retainedOwnerFinalFineShading D C q cell hcell selected).carrier i) := by
  classical
  simp [activeRetainedOwnerCellIndices]

/-- The owner of a retained fine index is in the selected logarithmic owner
bucket by the definition of the retained source subtype. -/
def selectedOwnerOfRetained
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (i : {i // i ∈ retainedOwnerSourceIndices C q}) :
    {s // s ∈ selectedOwnerLogBucket C q} :=
  ⟨C.owner i.1, (mem_retainedOwnerSourceIndices C q i.1).1 i.2⟩

/-- A literal point in the nonempty restricted fine carrier. -/
def activeCellCommonPoint
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    Space :=
  Classical.choose <|
    (mem_activeRetainedOwnerCellIndices D C q cell hcell selected i.1).1 i.2

theorem activeCellCommonPoint_mem_fine
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    activeCellCommonPoint D C q cell hcell selected i ∈
      (retainedOwnerFinalFineShading D C q cell hcell selected).carrier i.1 :=
  Classical.choose_spec <|
    (mem_activeRetainedOwnerCellIndices D C q cell hcell selected i.1).1 i.2

/-- The same chosen point lies in the restricted induced shading of the
constructed owner.  This is the exact fine/coarse common-point witness needed
to invoke the CubeWeight dense-ball conclusion. -/
theorem activeCellCommonPoint_mem_coarse
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    activeCellCommonPoint D C q cell hcell selected i ∈
      (retainedOwnerFinalCoarseShading D C q cell hcell selected).carrier
        (selectedOwnerOfRetained C q i.1) := by
  have hx := activeCellCommonPoint_mem_fine
    D C q cell hcell selected i
  simp only [retainedOwnerFinalFineShading,
    retainedOwnerFinalCoarseShading, restrictToCells_carrier] at hx ⊢
  refine ⟨?_, hx.2⟩
  apply sourceCarrier_subset_ownerFiberInducedCarrier
    C (selectedOwnerOfRetained C q i.1).1 i.1.1
  · exact (mem_ownerFiber C _ _).2 rfl
  · simpa only [retainedOwnerPlankFamily_shading_carrier] using hx.1

theorem activeCellCommonPoint_mem_coarseShadedUnion
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    activeCellCommonPoint D C q cell hcell selected i ∈
      (retainedOwnerFinalCoarseShading D C q cell hcell selected).shadedUnion :=
  Set.mem_iUnion.mpr ⟨selectedOwnerOfRetained C q i.1,
    activeCellCommonPoint_mem_coarse D C q cell hcell selected i⟩

/-- Any pointwise lower bound on the final coarse shaded union now has an
honest per-active-fine-index ball witness, with the center simultaneously in
the fine and coarse restricted shadings. -/
theorem exists_activeFine_commonPoint_denseBall
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (rho : NNReal) (lower : ENNReal)
    (hball : ∀ x ∈
      (retainedOwnerFinalCoarseShading D C q cell hcell selected).shadedUnion,
        lower ≤ volume
          ((retainedOwnerFinalFineShading D C q cell hcell selected).shadedUnion ∩
            Metric.ball x (rho : Real)))
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    ∃ x : Space,
      x ∈ (retainedOwnerFinalFineShading D C q cell hcell selected).carrier i.1 ∧
      x ∈ (retainedOwnerFinalCoarseShading D C q cell hcell selected).carrier
        (selectedOwnerOfRetained C q i.1) ∧
      lower ≤ volume
        ((retainedOwnerFinalFineShading D C q cell hcell selected).shadedUnion ∩
          Metric.ball x (rho : Real)) := by
  refine ⟨activeCellCommonPoint D C q cell hcell selected i,
    activeCellCommonPoint_mem_fine D C q cell hcell selected i,
    activeCellCommonPoint_mem_coarse D C q cell hcell selected i, ?_⟩
  exact hball _
    (activeCellCommonPoint_mem_coarseShadedUnion
      D C q cell hcell selected i)

/-- The fine plank is contained in its literal selected-owner thickening. -/
theorem activeFineBody_subset_ownerThickenedBody
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    (D.family i.1.1 : Set Space) ⊆
      (ownerThickenedBody D theta (selectedOwnerOfRetained C q i.1).1 : Set Space) := by
  have hiFiber : i.1.1 ∈ ownerFiber C (selectedOwnerOfRetained C q i.1).1 :=
    (mem_ownerFiber C _ _).2 rfl
  have hiThick := ownerFiber_subset_thickenedPlankIndices
    C (selectedOwnerOfRetained C q i.1).1 hiFiber
  simpa only [coe_ownerThickenedBody] using
    (mem_thickenedPlankIndices_iff D theta
      (selectedOwnerOfRetained C q i.1).1 i.1.1).1 hiThick

/-- Mutual comparability supplies the reverse controlled containment of the
owner's unthickened body in the fine plank's radius-`theta*b` thickening. -/
theorem activeOwnerBody_subset_fineThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    (D.family (selectedOwnerOfRetained C q i.1).1 : Set Space) ⊆
      Metric.cthickening ((theta * b : NNReal) : Real)
        (D.family i.1.1 : Set Space) := by
  rcases C.owner_eq_or_comparable i.1.1 with heq | hcomp
  · simpa only [selectedOwnerOfRetained, heq] using
      (Metric.self_subset_cthickening
        (δ := ((theta * b : NNReal) : Real))
        (D.family i.1.1 : Set Space))
  · exact (mem_thickenedPlankIndices_iff D theta i.1.1
      (selectedOwnerOfRetained C q i.1).1).1 hcomp.2

/-- Thickening the owner once more costs exactly a doubled radius around the
fine plank; no free container or geometric callback is used. -/
theorem activeOwnerThickenedBody_subset_doubleFineThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected}) :
    (ownerThickenedBody D theta (selectedOwnerOfRetained C q i.1).1 : Set Space) ⊆
      Metric.cthickening (2 * ((theta * b : NNReal) : Real))
        (D.family i.1.1 : Set Space) := by
  rw [coe_ownerThickenedBody]
  let r : Real := ((theta * b : NNReal) : Real)
  have howner : (D.family (selectedOwnerOfRetained C q i.1).1 : Set Space) ⊆
      Metric.cthickening r (D.family i.1.1 : Set Space) := by
    simpa only [r] using activeOwnerBody_subset_fineThickening
      D C q cell hcell selected i
  calc
    Metric.cthickening r
        (D.family (selectedOwnerOfRetained C q i.1).1 : Set Space) ⊆
      Metric.cthickening r
        (Metric.cthickening r (D.family i.1.1 : Set Space)) :=
          Metric.cthickening_subset_of_subset r howner
    _ ⊆ Metric.cthickening (r + r) (D.family i.1.1 : Set Space) :=
      Metric.cthickening_cthickening_subset (by positivity) (by positivity) _
    _ = Metric.cthickening (2 * r) (D.family i.1.1 : Set Space) := by
      congr 2
      ring

/-- The canonical slab containing an active fine member also controls its
thickened owner after the explicit double-radius enlargement. -/
theorem activeOwnerThickenedBody_subset_certifiedSlabThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    {tau : NNReal} {S : ConvexBody Space} (hS : IsSlab 1 tau S)
    (i : {i // i ∈ activeRetainedOwnerCellIndices D C q cell hcell selected})
    (hi : i.1 ∈
      (retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
        D C q cell hcell selected hmass).members tau S) :
    (ownerThickenedBody D theta (selectedOwnerOfRetained C q i.1).1 : Set Space) ⊆
      Metric.cthickening (2 * ((theta * b : NNReal) : Real))
        (S : Set Space) := by
  let R := retainedOwnerCellRestrictedCanonicalUnitSlabIncidence
    D C q cell hcell selected hmass
  have hFineS :
      (D.family i.1.1 : Set Space) ⊆ (S : Set Space) := by
    have htangent := (R.mem_members_of_isSlab hS i.1).1 hi
    simpa only [retainedOwnerCellRestrictedPlankDatum_family,
      retainedOwnerPlankFamily_family_apply] using htangent.1
  exact (activeOwnerThickenedBody_subset_doubleFineThickening
    D C q cell hcell selected i).trans
      (Metric.cthickening_subset_of_subset
        (2 * ((theta * b : NNReal) : Real)) hFineS)

#print axioms activeCellCommonPoint_mem_fine
#print axioms activeCellCommonPoint_mem_coarse
#print axioms exists_activeFine_commonPoint_denseBall
#print axioms activeFineBody_subset_ownerThickenedBody
#print axioms activeOwnerThickenedBody_subset_doubleFineThickening
#print axioms activeOwnerThickenedBody_subset_certifiedSlabThickening

end
end Family8PlankRetainedOwnerActiveCellCommonBallContainerV1
