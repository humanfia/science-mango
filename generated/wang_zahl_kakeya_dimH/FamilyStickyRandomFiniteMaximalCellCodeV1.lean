import FamilyStickyRandomFiniteCollisionRefinementV1
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.Powerset

open Set
open scoped BigOperators

namespace FamilyStickyRandomFiniteMaximalCellCodeV1

noncomputable section
set_option linter.unusedSectionVars false

/-!
# A finite maximal separated cell code

For a symmetric separation relation on a finite occurrence type, choose a
maximal pairwise separated set.  Every occurrence is either already a cell
centre or fails separation from some centre.  Coding it by such a centre is
the exact combinatorial step used after the finite `100 T₀` union bound in
GWZ `lemrandommotion`, pinned source lines 2655--2677.

This module is purely finite: the later tube adapter must prove that failure
of separation implies carrier containment in the corresponding dilated model
tube.  No geometric collision conclusion is assumed here.
-/

variable {occurrence : Type*} [Fintype occurrence] [DecidableEq occurrence]

structure MaximalSeparatedCells (separated : occurrence -> occurrence -> Prop) where
  cells : Finset occurrence
  pairwise : Set.Pairwise (cells : Set occurrence) separated
  cover : forall a, a ∈ cells ∨ exists b, b ∈ cells ∧ ¬ separated a b

theorem exists_maximalSeparatedCells
    (separated : occurrence -> occurrence -> Prop)
    (hsymm : Std.Symm separated) :
    Nonempty (MaximalSeparatedCells separated) := by
  classical
  let p : Finset occurrence -> Prop :=
    fun S => Set.Pairwise (S : Set occurrence) separated
  have hpempty : p ∅ := by
    simp [p]
  obtain ⟨S, _hempty, hmax⟩ :=
    Finite.exists_le_maximal (p := p) (a := (∅ : Finset occurrence)) hpempty
  have hpair : Set.Pairwise (S : Set occurrence) separated := hmax.1
  refine ⟨{
    cells := S
    pairwise := hpair
    cover := ?_ }⟩
  intro a
  by_cases ha : a ∈ S
  · exact Or.inl ha
  · right
    by_contra hnone
    push Not at hnone
    have hinsertPairwise :
        Set.Pairwise ((insert a S : Finset occurrence) : Set occurrence)
          separated := by
      rw [Finset.coe_insert]
      exact hpair.insert (fun b hb _hab =>
        ⟨hnone b hb, hsymm.symm _ _ (hnone b hb)⟩)
    have hpinsert : p (insert a S) := hinsertPairwise
    have hsubset : S ⊆ insert a S := Finset.subset_insert a S
    have hinsertSubset : insert a S ⊆ S := hmax.2 hpinsert hsubset
    exact ha (hinsertSubset (Finset.mem_insert_self a S))

namespace MaximalSeparatedCells

variable {separated : occurrence -> occurrence -> Prop}
  (C : MaximalSeparatedCells separated)

/-- The occupied model cells, represented by their selected centres. -/
abbrev Cell := {b // b ∈ C.cells}

/-- Assign every occurrence to itself when it is a centre, and otherwise to
one centre witnessing failure of separation. -/
def code (a : occurrence) : C.Cell :=
  if h : a ∈ C.cells then
    ⟨a, h⟩
  else
    ⟨Classical.choose ((C.cover a).resolve_left h),
      (Classical.choose_spec ((C.cover a).resolve_left h)).1⟩

@[simp] theorem code_eq_self_of_mem {a : occurrence} (ha : a ∈ C.cells) :
    (C.code a).1 = a := by
  simp [code, ha]

theorem eq_or_not_separated_code (a : occurrence) :
    a = (C.code a).1 ∨ ¬ separated a (C.code a).1 := by
  by_cases ha : a ∈ C.cells
  · left
    simp [C.code_eq_self_of_mem ha]
  · right
    simpa [code, ha] using
      (Classical.choose_spec ((C.cover a).resolve_left ha)).2

theorem pairwise_cell_centres :
    Set.Pairwise (Set.univ : Set C.Cell) fun b c =>
      separated b.1 c.1 := by
  intro b _hb c _hc hbc
  apply C.pairwise b.2 c.2
  intro h
  apply hbc
  exact Subtype.ext h

/-- Package a proved uniform cell-fibre bound for the already audited
bounded-collision refinement theorem. -/
def toBoundedCollisionCode
    [DecidableEq C.Cell] (M : Nat)
    (hfiber : forall b : C.Cell,
      (Finset.univ.filter fun a => C.code a = b).card <= M) :
    FamilyStickyRandomFiniteCollisionRefinementV1.BoundedCollisionCode
      (occurrence := occurrence) (codeType := C.Cell) where
  code := C.code
  multiplicity := M
  fiber_card_le := fun b _hb => hfiber b

theorem card_le_of_fiber_bound
    [DecidableEq C.Cell] (M : Nat)
    (hfiber : forall b : C.Cell,
      (Finset.univ.filter fun a => C.code a = b).card <= M) :
    Fintype.card occurrence <= M * Fintype.card C.Cell := by
  have h :=
    FamilyStickyRandomFiniteCollisionRefinementV1.BoundedCollisionCode.card_le_multiplicity_mul_card_image
      C.code M (fun b _hb => hfiber b)
  calc
    Fintype.card occurrence <=
        M * (Finset.univ.image C.code).card := h
    _ <= M * Fintype.card C.Cell :=
      Nat.mul_le_mul_left M (Finset.card_le_univ _)

#print axioms exists_maximalSeparatedCells
#print axioms MaximalSeparatedCells.code_eq_self_of_mem
#print axioms MaximalSeparatedCells.eq_or_not_separated_code
#print axioms MaximalSeparatedCells.pairwise_cell_centres
#print axioms MaximalSeparatedCells.card_le_of_fiber_bound

end MaximalSeparatedCells

end
end FamilyStickyRandomFiniteMaximalCellCodeV1
