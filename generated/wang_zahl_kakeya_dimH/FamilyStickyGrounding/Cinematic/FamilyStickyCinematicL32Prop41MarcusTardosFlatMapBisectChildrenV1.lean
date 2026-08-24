import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosFlatMapBisectChildrenV1

open FamilyStickyCinematicL32Prop41MarcusTardosDyadicBlocksV1

/-! # Position identities for a flat map of literal bisections -/

@[simp]
theorem length_flatMap_bisect {α : Type*} (blocks : List (List α)) :
    (blocks.flatMap bisect).length = 2 * blocks.length := by
  induction blocks with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.length_append, length_bisect,
        List.length_cons, ih]
      omega

def leftChildIndex {α : Type*} (blocks : List (List α))
    (i : Fin blocks.length) : Fin (blocks.flatMap bisect).length :=
  ⟨2 * i.1, by
    rw [length_flatMap_bisect]
    omega⟩

def rightChildIndex {α : Type*} (blocks : List (List α))
    (i : Fin blocks.length) : Fin (blocks.flatMap bisect).length :=
  ⟨2 * i.1 + 1, by
    rw [length_flatMap_bisect]
    omega⟩

@[simp]
theorem flatMap_bisect_get_left
    {α : Type*} (blocks : List (List α)) (i : Fin blocks.length) :
    (blocks.flatMap bisect).get (leftChildIndex blocks i) =
      (blocks.get i).take (((blocks.get i).length + 1) / 2) := by
  induction blocks with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => simp [leftChildIndex, bisect]
      | succ i =>
          simpa [leftChildIndex, bisect, Nat.mul_succ] using
            (ih (⟨i, by simpa using hi⟩ : Fin tail.length))

@[simp]
theorem flatMap_bisect_get_right
    {α : Type*} (blocks : List (List α)) (i : Fin blocks.length) :
    (blocks.flatMap bisect).get (rightChildIndex blocks i) =
      (blocks.get i).drop (((blocks.get i).length + 1) / 2) := by
  induction blocks with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
      rcases i with ⟨i, hi⟩
      cases i with
      | zero => simp [rightChildIndex, bisect]
      | succ i =>
          simpa [rightChildIndex, bisect, Nat.mul_succ] using
            (ih (⟨i, by simpa using hi⟩ : Fin tail.length))

theorem child_eq_left_or_right_of_mem_bisect
    {α : Type*} (blocks : List (List α)) (i : Fin blocks.length)
    (child : List α) (hchild : child ∈ bisect (blocks.get i)) :
    child = (blocks.flatMap bisect).get (leftChildIndex blocks i) ∨
      child = (blocks.flatMap bisect).get (rightChildIndex blocks i) := by
  simp [bisect] at hchild
  rcases hchild with rfl | rfl
  · exact Or.inl (flatMap_bisect_get_left blocks i).symm
  · exact Or.inr (flatMap_bisect_get_right blocks i).symm

#print axioms length_flatMap_bisect
#print axioms leftChildIndex
#print axioms rightChildIndex
#print axioms flatMap_bisect_get_left
#print axioms flatMap_bisect_get_right
#print axioms child_eq_left_or_right_of_mem_bisect

end FamilyStickyCinematicL32Prop41MarcusTardosFlatMapBisectChildrenV1
