import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDoubleCrossCoreCleanV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosPartitionOccurrenceUniqueV1

open FamilyStickyCinematicL32Prop41MarcusTardosPartitionBlockIntervalV1

/-! # Unique position-indexed block containing a flattened occurrence -/

theorem exists_unique_partitionBlock_mem
    {α : Type*} {blocks : List (List α)} {a : α}
    (hflat : blocks.flatten.Nodup) (ha : a ∈ blocks.flatten) :
    ∃! i : Fin blocks.length, a ∈ partitionBlock blocks i := by
  obtain ⟨block, hblock, hablock⟩ := List.mem_flatten.mp ha
  obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hblock
  let i : Fin blocks.length := ⟨n, hn⟩
  have hi : a ∈ partitionBlock blocks i := by
    simpa [partitionBlock, i, hget] using hablock
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply Fin.ext
  by_contra hne
  have hpair := (List.nodup_flatten.mp hflat).2
  rcases lt_or_gt_of_ne hne with hji | hij
  · have hdisjoint := (List.pairwise_iff_getElem.mp hpair)
        j.1 i.1 j.2 i.2 hji
    exact (List.disjoint_left.mp hdisjoint) hj hi
  · have hdisjoint := (List.pairwise_iff_getElem.mp hpair)
        i.1 j.1 i.2 j.2 hij
    exact (List.disjoint_left.mp hdisjoint) hi hj

noncomputable def partitionIndexOf
    {α : Type*} {blocks : List (List α)} {a : α}
    (hflat : blocks.flatten.Nodup) (ha : a ∈ blocks.flatten) :
    Fin blocks.length :=
  Classical.choose (exists_unique_partitionBlock_mem hflat ha)

theorem mem_partitionBlock_partitionIndexOf
    {α : Type*} {blocks : List (List α)} {a : α}
    (hflat : blocks.flatten.Nodup) (ha : a ∈ blocks.flatten) :
    a ∈ partitionBlock blocks (partitionIndexOf hflat ha) :=
  (Classical.choose_spec (exists_unique_partitionBlock_mem hflat ha)).1

theorem partitionIndexOf_eq_of_mem
    {α : Type*} {blocks : List (List α)} {a : α}
    (hflat : blocks.flatten.Nodup) (ha : a ∈ blocks.flatten)
    (i : Fin blocks.length) (hi : a ∈ partitionBlock blocks i) :
    partitionIndexOf hflat ha = i :=
  ((Classical.choose_spec (exists_unique_partitionBlock_mem hflat ha)).2 i hi).symm

#print axioms exists_unique_partitionBlock_mem
#print axioms partitionIndexOf
#print axioms mem_partitionBlock_partitionIndexOf
#print axioms partitionIndexOf_eq_of_mem

end FamilyStickyCinematicL32Prop41MarcusTardosPartitionOccurrenceUniqueV1
