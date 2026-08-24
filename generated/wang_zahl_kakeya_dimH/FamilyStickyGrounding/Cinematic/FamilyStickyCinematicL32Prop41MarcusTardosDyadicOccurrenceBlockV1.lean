import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1

open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
open FamilyStickyCinematicL32Prop41MarcusTardosLinearRestrictionV1

/-!
# The unique dyadic block containing a fixed occurrence

The blocks are indexed by positions in the block list, so repeated empty
blocks remain distinct.  Nodup of the original sequence nevertheless makes
the index of the block containing an actual symbol unique.
-/

theorem blockAt_nodup
    {α : Type*} {depth : Nat} {l : List α}
    (hl : l.Nodup) (i : BlockIndex depth l) :
    (blockAt depth l i).Nodup := by
  have hflat : (dyadicBlocks depth l).flatten.Nodup := by
    simpa using hl
  exact (List.nodup_flatten.mp hflat).1 _ (blockAt_mem depth l i)

theorem exists_unique_blockIndex_mem
    {α : Type*} {depth : Nat} {l : List α} {x : α}
    (hl : l.Nodup) (hx : x ∈ l) :
    ∃! i : BlockIndex depth l, x ∈ blockAt depth l i := by
  have hxflat : x ∈ (dyadicBlocks depth l).flatten := by
    simpa using hx
  obtain ⟨block, hblock, hxblock⟩ := List.mem_flatten.mp hxflat
  obtain ⟨n, hn, hget⟩ := List.getElem_of_mem hblock
  let i : BlockIndex depth l := ⟨n, hn⟩
  have hi : x ∈ blockAt depth l i := by
    simpa [blockAt, i, hget] using hxblock
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply Fin.ext
  by_contra hne
  have hflat : (dyadicBlocks depth l).flatten.Nodup := by
    simpa using hl
  have hpair := (List.nodup_flatten.mp hflat).2
  rcases lt_or_gt_of_ne hne with hji | hij
  · have hdisjoint := (List.pairwise_iff_getElem.mp hpair)
        j.1 i.1 j.2 i.2 hji
    exact (List.disjoint_left.mp hdisjoint) hj hi
  · have hdisjoint := (List.pairwise_iff_getElem.mp hpair)
        i.1 j.1 i.2 j.2 hij
    exact (List.disjoint_left.mp hdisjoint) hi hj

noncomputable def blockIndexOf
    {α : Type*} {depth : Nat} {l : List α} {x : α}
    (hl : l.Nodup) (hx : x ∈ l) : BlockIndex depth l :=
  Classical.choose (exists_unique_blockIndex_mem hl hx)

theorem mem_blockAt_blockIndexOf
    {α : Type*} {depth : Nat} {l : List α} {x : α}
    (hl : l.Nodup) (hx : x ∈ l) :
    x ∈ blockAt depth l (blockIndexOf hl hx) :=
  (Classical.choose_spec (exists_unique_blockIndex_mem hl hx)).1

theorem blockIndexOf_eq_of_mem
    {α : Type*} {depth : Nat} {l : List α} {x : α}
    (hl : l.Nodup) (hx : x ∈ l) (i : BlockIndex depth l)
    (hi : x ∈ blockAt depth l i) :
    blockIndexOf hl hx = i :=
  ((Classical.choose_spec (exists_unique_blockIndex_mem hl hx)).2 i hi).symm

noncomputable def occurrenceBlock
    {α : Type*} (depth : Nat) (l : List α) (hl : l.Nodup)
    (x : α) (hx : x ∈ l) : List α :=
  blockAt depth l (blockIndexOf hl hx)

@[simp]
theorem mem_occurrenceBlock
    {α : Type*} (depth : Nat) (l : List α) (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    x ∈ occurrenceBlock depth l hl x hx :=
  mem_blockAt_blockIndexOf hl hx

theorem occurrenceBlock_nodup
    {α : Type*} (depth : Nat) (l : List α) (hl : l.Nodup)
    (x : α) (hx : x ∈ l) :
    (occurrenceBlock depth l hl x hx).Nodup :=
  blockAt_nodup hl _

noncomputable def occurrenceLinearBlock
    {α : Type*} (depth : Nat) (l : List α) (hl : l.Nodup)
    (x : α) (hx : x ∈ l) : DistinctLinearSequence α where
  order := occurrenceBlock depth l hl x hx
  nodup_order := occurrenceBlock_nodup depth l hl x hx

#print axioms blockAt_nodup
#print axioms exists_unique_blockIndex_mem
#print axioms mem_blockAt_blockIndexOf
#print axioms blockIndexOf_eq_of_mem
#print axioms occurrenceBlock
#print axioms occurrenceLinearBlock

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicOccurrenceBlockV1
