import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1

/-!
# Explicit recursive dyadic blocks

This is the literal block construction used in Marcus--Tardos Theorem 1:
each linear block is split into two consecutive almost-equal halves.  The
first frozen layer proves exact block count and exact reconstruction of the
original list.
-/

/-- Two consecutive halves; the left half receives the extra element when
the length is odd. -/
def bisect {α : Type*} (l : List α) : List (List α) :=
  [l.take ((l.length + 1) / 2), l.drop ((l.length + 1) / 2)]

@[simp]
theorem length_bisect {α : Type*} (l : List α) :
    (bisect l).length = 2 := rfl

@[simp]
theorem flatten_bisect {α : Type*} (l : List α) :
    (bisect l).flatten = l := by
  simp [bisect, List.take_append_drop]

/-- Level `depth` of the recursive dyadic subdivision. -/
def dyadicBlocks {α : Type*} : Nat → List α → List (List α)
  | 0, l => [l]
  | depth + 1, l => (dyadicBlocks depth l).flatMap bisect

theorem flatten_flatMap_bisect {α : Type*} (blocks : List (List α)) :
    (blocks.flatMap bisect).flatten = blocks.flatten := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, List.flatten_append, flatten_bisect, ih,
        List.flatten_cons]

@[simp]
theorem length_dyadicBlocks {α : Type*} (depth : Nat) (l : List α) :
    (dyadicBlocks depth l).length = 2 ^ depth := by
  induction depth with
  | zero => simp [dyadicBlocks]
  | succ depth ih =>
      simp [dyadicBlocks, List.length_flatMap, ih, pow_succ]

@[simp]
theorem flatten_dyadicBlocks {α : Type*} (depth : Nat) (l : List α) :
    (dyadicBlocks depth l).flatten = l := by
  induction depth with
  | zero => simp [dyadicBlocks]
  | succ depth ih =>
      rw [dyadicBlocks, flatten_flatMap_bisect, ih]

/-- Every next-level block lies in the bisection of an actual parent block. -/
theorem mem_dyadicBlocks_succ_iff
    {α : Type*} {depth : Nat} {l child : List α} :
    child ∈ dyadicBlocks (depth + 1) l ↔
      ∃ parent ∈ dyadicBlocks depth l, child ∈ bisect parent := by
  simp [dyadicBlocks]

#print axioms bisect
#print axioms length_bisect
#print axioms flatten_bisect
#print axioms length_dyadicBlocks
#print axioms flatten_dyadicBlocks
#print axioms mem_dyadicBlocks_succ_iff

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
