import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1

/-!
# Dyadic blocks partition the induced common order

Filtering every literal dyadic block by the other cyclic sequence's support
and then flattening gives exactly the induced common order.  This is the
faithful partition input for the rotation-cut proof of Marcus--Tardos Lemma 2.
-/

theorem flatten_map_filter
    {α : Type*} (blocks : List (List α)) (p : α → Bool) :
    (blocks.map fun block => block.filter p).flatten =
      blocks.flatten.filter p := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.flatten_cons, List.filter_append, ih]

def commonBlocks
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :
    List (List symbol) :=
  (dyadicBlocks depth A.order).map fun block =>
    block.filter fun a => a ∈ B.support

@[simp]
theorem length_commonBlocks
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :
    (commonBlocks depth A B).length = 2 ^ depth := by
  simp [commonBlocks]

@[simp]
theorem flatten_commonBlocks
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :
    (commonBlocks depth A B).flatten = A.commonOrder B := by
  rw [commonBlocks, flatten_map_filter, flatten_dyadicBlocks]
  rfl

theorem flatten_commonBlocks_nodup
    {symbol : Type*} [DecidableEq symbol]
    (depth : Nat) (A B : DistinctCyclicSequence symbol) :
    (commonBlocks depth A B).flatten.Nodup := by
  rw [flatten_commonBlocks]
  exact commonOrder_nodup A B

#print axioms flatten_map_filter
#print axioms commonBlocks
#print axioms length_commonBlocks
#print axioms flatten_commonBlocks
#print axioms flatten_commonBlocks_nodup

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicCommonOrderPartitionV1
