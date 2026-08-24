import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockRealSizeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDiagonalBlockBoundV1
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1

open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlockRealSizeV1
open FamilyStickyCinematicL32Prop41MarcusTardosDiagonalBlockBoundV1

/-!
# Actual dyadic-block diagonal estimate

Blocks are indexed by their list positions, not by their contents; this keeps
distinct empty blocks distinct and makes the count faithful.
-/

abbrev BlockIndex {α : Type*} (depth : Nat) (l : List α) :=
  Fin (dyadicBlocks depth l).length

def blockAt {α : Type*} (depth : Nat) (l : List α)
    (i : BlockIndex depth l) : List α :=
  (dyadicBlocks depth l)[i.1]

theorem blockAt_mem {α : Type*} (depth : Nat) (l : List α)
    (i : BlockIndex depth l) :
    blockAt depth l i ∈ dyadicBlocks depth l := by
  exact List.getElem_mem _

theorem sum_blockAt_length {α : Type*} (depth : Nat) (l : List α) :
    (∑ i : BlockIndex depth l, (blockAt depth l i).length) = l.length := by
  simp only [blockAt]
  rw [Fin.sum_univ_fun_getElem]
  rw [← List.length_flatten, flatten_dyadicBlocks]

/-- Exact source diagonal bound at one level. -/
theorem sum_block_orderedPairs_le_sq_div_pow
    {α : Type*} (depth : Nat) (l : List α) :
    (∑ i : BlockIndex depth l,
      ((blockAt depth l i).length : Real) *
        (((blockAt depth l i).length : Real) - 1)) ≤
      (l.length : Real) ^ 2 / (2 : Real) ^ depth := by
  apply sum_size_mul_pred_le_sq_div
    (fun i : BlockIndex depth l => ((blockAt depth l i).length : Real))
    (l.length : Real) ((2 : Real) ^ depth)
  · intro i
    positivity
  · norm_cast
    exact sum_blockAt_length depth l
  · intro i
    simpa using length_sub_one_le_div_pow (blockAt_mem depth l i)

#print axioms blockAt
#print axioms blockAt_mem
#print axioms sum_blockAt_length
#print axioms sum_block_orderedPairs_le_sq_div_pow

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
