import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1

noncomputable section

universe u v

/-!
# A measurable first-hit partition of a finite cover

For a finite family of measurable events covering a measurable source set,
choose a fixed enumeration of the finite index set and assign each source
point to the first event containing it.  The resulting fibres are measurable,
pairwise disjoint, cover the source exactly, and their measures sum to the
source measure.

This is the pure continuum partition used to define the paper's shadings
`Y₂(R)` once the geometric cover by fine rectangles is available.
-/

/-- A fixed, noncomputable enumeration rank on a finite index set.  Values
outside `items` are irrelevant. -/
noncomputable def finiteFirstHitRank
    {index : Type v} [DecidableEq index]
    (items : Finset index) (i : index) : Nat :=
  if hi : i ∈ items then (items.equivFin ⟨i, hi⟩).1 else items.card

/-- The fixed enumeration rank is injective on the finite carrier. -/
theorem finiteFirstHitRank_injOn
    {index : Type v} [DecidableEq index]
    (items : Finset index) :
    Set.InjOn (finiteFirstHitRank items) (items : Set index) := by
  classical
  intro i hi j hj hij
  change i ∈ items at hi
  change j ∈ items at hj
  have hij' := hij
  rw [finiteFirstHitRank, dif_pos hi,
    finiteFirstHitRank, dif_pos hj] at hij'
  have hfin : items.equivFin ⟨i, hi⟩ = items.equivFin ⟨j, hj⟩ := by
    apply Fin.ext
    exact hij'
  exact congrArg Subtype.val (items.equivFin.injective hfin)

/-- Union of all events whose fixed rank precedes `i`. -/
noncomputable def finiteEarlierHitSet
    {point : Type u} {index : Type v} [DecidableEq index]
    (items : Finset index) (event : index -> Set point) (i : index) :
    Set point :=
  ⋃ j ∈ ((items.filter fun j =>
    finiteFirstHitRank items j < finiteFirstHitRank items i) : Set index),
      event j

/-- The part of `source ∩ event i` not captured by an earlier event. -/
noncomputable def finiteFirstHitFiber
    {point : Type u} {index : Type v} [DecidableEq index]
    (source : Set point) (items : Finset index)
    (event : index -> Set point) (i : index) : Set point :=
  if i ∈ items then
    (source ∩ event i) \ finiteEarlierHitSet items event i
  else ∅

theorem mem_finiteEarlierHitSet_iff
    {point : Type u} {index : Type v} [DecidableEq index]
    (items : Finset index) (event : index -> Set point)
    (i : index) (x : point) :
    x ∈ finiteEarlierHitSet items event i ↔
      exists j, j ∈ items ∧
        finiteFirstHitRank items j < finiteFirstHitRank items i ∧
        x ∈ event j := by
  classical
  simp [finiteEarlierHitSet, and_assoc]

theorem mem_finiteFirstHitFiber_iff
    {point : Type u} {index : Type v} [DecidableEq index]
    (source : Set point) (items : Finset index)
    (event : index -> Set point) (i : index) (x : point) :
    x ∈ finiteFirstHitFiber source items event i ↔
      i ∈ items ∧ x ∈ source ∧ x ∈ event i ∧
        forall j, j ∈ items ->
          finiteFirstHitRank items j < finiteFirstHitRank items i ->
            x ∉ event j := by
  classical
  by_cases hi : i ∈ items
  · simp only [finiteFirstHitFiber, hi, if_pos, Set.mem_sdiff, mem_inter_iff]
    rw [mem_finiteEarlierHitSet_iff]
    simp only [true_and]
    constructor
    · rintro ⟨⟨hxSource, hxEvent⟩, hnotEarlier⟩
      refine ⟨hxSource, hxEvent, ?_⟩
      intro j hj hrank hxj
      exact hnotEarlier ⟨j, hj, hrank, hxj⟩
    · rintro ⟨hxSource, hxEvent, hminimal⟩
      refine ⟨⟨hxSource, hxEvent⟩, ?_⟩
      rintro ⟨j, hj, hrank, hxj⟩
      exact hminimal j hj hrank hxj
  · simp [finiteFirstHitFiber, hi]

/-- A finite union of measurable events is measurable. -/
theorem measurableSet_finiteBiUnion
    {point : Type u} [MeasurableSpace point]
    {index : Type v} [DecidableEq index]
    (items : Finset index) (event : index -> Set point)
    (hmeasurable : forall i, i ∈ items -> MeasurableSet (event i)) :
    MeasurableSet (⋃ i ∈ (items : Set index), event i) := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert i items hi ih =>
      have hiMeasurable : MeasurableSet (event i) :=
        hmeasurable i (Finset.mem_insert_self i items)
      have hitemsMeasurable : forall j, j ∈ items ->
          MeasurableSet (event j) := by
        intro j hj
        exact hmeasurable j (Finset.mem_insert_of_mem hj)
      simpa using hiMeasurable.union (ih hitemsMeasurable)

theorem measurableSet_finiteEarlierHitSet
    {point : Type u} [MeasurableSpace point]
    {index : Type v} [DecidableEq index]
    (items : Finset index) (event : index -> Set point)
    (hmeasurable : forall i, i ∈ items -> MeasurableSet (event i))
    (i : index) :
    MeasurableSet (finiteEarlierHitSet items event i) := by
  classical
  apply measurableSet_finiteBiUnion
  intro j hj
  exact hmeasurable j (Finset.filter_subset _ _ hj)

theorem measurableSet_finiteFirstHitFiber
    {point : Type u} [MeasurableSpace point]
    {index : Type v} [DecidableEq index]
    (source : Set point) (items : Finset index)
    (event : index -> Set point)
    (hsource : MeasurableSet source)
    (hmeasurable : forall i, i ∈ items -> MeasurableSet (event i))
    (i : index) :
    MeasurableSet (finiteFirstHitFiber source items event i) := by
  classical
  by_cases hi : i ∈ items
  · rw [finiteFirstHitFiber, if_pos hi]
    exact (hsource.inter (hmeasurable i hi)).diff
      (measurableSet_finiteEarlierHitSet items event hmeasurable i)
  · rw [finiteFirstHitFiber, if_neg hi]
    exact MeasurableSet.empty

theorem finiteFirstHitFiber_subset_source
    {point : Type u} {index : Type v} [DecidableEq index]
    (source : Set point) (items : Finset index)
    (event : index -> Set point) (i : index) :
    finiteFirstHitFiber source items event i ⊆ source := by
  classical
  intro x hx
  exact (mem_finiteFirstHitFiber_iff source items event i x).mp hx |>.2.1

theorem finiteFirstHitFiber_subset_event
    {point : Type u} {index : Type v} [DecidableEq index]
    (source : Set point) (items : Finset index)
    (event : index -> Set point) (i : index) :
    finiteFirstHitFiber source items event i ⊆ event i := by
  classical
  intro x hx
  exact (mem_finiteFirstHitFiber_iff source items event i x).mp hx |>.2.2.1

/-- First-hit fibres over the finite carrier are pairwise disjoint. -/
theorem finiteFirstHitFibers_pairwiseDisjoint
    {point : Type u} {index : Type v} [DecidableEq index]
    (source : Set point) (items : Finset index)
    (event : index -> Set point) :
    Set.PairwiseDisjoint (items : Set index)
      (finiteFirstHitFiber source items event) := by
  classical
  intro i hi j hj hij
  change Disjoint (finiteFirstHitFiber source items event i)
    (finiteFirstHitFiber source items event j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hiData :=
    (mem_finiteFirstHitFiber_iff source items event i x).mp hxi
  have hjData :=
    (mem_finiteFirstHitFiber_iff source items event j x).mp hxj
  have hrankNe :
      finiteFirstHitRank items i ≠ finiteFirstHitRank items j := by
    intro hrank
    exact hij (finiteFirstHitRank_injOn items hi hj hrank)
  rcases lt_or_gt_of_ne hrankNe with hijRank | hjiRank
  · exact (hjData.2.2.2 i hi hijRank) hiData.2.2.1
  · exact (hiData.2.2.2 j hj hjiRank) hjData.2.2.1

/-- A literal finite event cover is partitioned exactly by first-hit fibres. -/
theorem biUnion_finiteFirstHitFiber_eq_source
    {point : Type u} {index : Type v} [DecidableEq index]
    (source : Set point) (items : Finset index)
    (event : index -> Set point)
    (hcover : forall x, x ∈ source ->
      exists i, i ∈ items ∧ x ∈ event i) :
    (⋃ i ∈ (items : Set index),
      finiteFirstHitFiber source items event i) = source := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨i, _hi, hxi⟩
    exact finiteFirstHitFiber_subset_source source items event i hxi
  · intro x hx
    let active := items.filter fun i => x ∈ event i
    have hactive : active.Nonempty := by
      obtain ⟨i, hi, hxi⟩ := hcover x hx
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩
    obtain ⟨i, hiActive, hminimal⟩ :=
      Finset.exists_min_image active (finiteFirstHitRank items) hactive
    have hiData := Finset.mem_filter.mp hiActive
    have hiFiber : x ∈ finiteFirstHitFiber source items event i := by
      apply (mem_finiteFirstHitFiber_iff source items event i x).mpr
      refine ⟨hiData.1, hx, hiData.2, ?_⟩
      intro j hj hjRank hxj
      have hjActive : j ∈ active :=
        Finset.mem_filter.mpr ⟨hj, hxj⟩
      exact (not_le_of_gt hjRank) (hminimal j hjActive)
    simp only [mem_iUnion]
    exact ⟨i, hiData.1, hiFiber⟩

/-- Exact source-mass decomposition over the measurable first-hit fibres. -/
theorem sum_measure_finiteFirstHitFiber_eq_source
    {point : Type u} [MeasurableSpace point]
    {index : Type v} [DecidableEq index]
    (mu : Measure point) (source : Set point) (items : Finset index)
    (event : index -> Set point)
    (hsource : MeasurableSet source)
    (hmeasurable : forall i, i ∈ items -> MeasurableSet (event i))
    (hcover : forall x, x ∈ source ->
      exists i, i ∈ items ∧ x ∈ event i) :
    (∑ i ∈ items, mu (finiteFirstHitFiber source items event i)) =
      mu source := by
  calc
    (∑ i ∈ items, mu (finiteFirstHitFiber source items event i)) =
        mu (⋃ i ∈ (items : Set index),
          finiteFirstHitFiber source items event i) :=
      (measure_biUnion_finset
        (finiteFirstHitFibers_pairwiseDisjoint source items event)
        (fun i _hi => measurableSet_finiteFirstHitFiber source items event
          hsource hmeasurable i)).symm
    _ = mu source := by
      rw [biUnion_finiteFirstHitFiber_eq_source source items event hcover]

#print axioms finiteFirstHitRank
#print axioms finiteFirstHitRank_injOn
#print axioms finiteEarlierHitSet
#print axioms finiteFirstHitFiber
#print axioms measurableSet_finiteFirstHitFiber
#print axioms finiteFirstHitFibers_pairwiseDisjoint
#print axioms biUnion_finiteFirstHitFiber_eq_source
#print axioms sum_measure_finiteFirstHitFiber_eq_source

end

end FamilyStickyCinematicL32Lemma55FiniteMeasurableFirstHitPartitionV1
