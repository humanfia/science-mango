import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Set
open scoped BigOperators

namespace FamilyStickyRandomFiniteCollisionRefinementV1

noncomputable section

/-!
# Bounded-collision refinement for a finite occurrence family

GWZ `lemrandommotion`, pinned source lines 2655--2677, proves bounded
multiplicity in each essentially-distinct tube cell; it does not prove that
the occurrence family is injectively parametrized.  This module records the
exact finite combinatorial consequence: a code with fibres of size at most
`M` has at least `#occurrences / M` represented cells, and choosing one
representative per cell gives a pairwise separated refinement whenever
different codes are geometrically separated.

The code is intentionally abstract here.  In the source it is supplied by a
finite net of model tubes `T₀` and the incidence condition `T ⊆ 100 T₀`.
No geometric collision estimate is smuggled into this counting lemma.
-/

variable {occurrence codeType : Type*}
  [Fintype occurrence] [DecidableEq codeType]

/-- A finite collision coding with a uniform fibre multiplicity bound. -/
structure BoundedCollisionCode where
  code : occurrence -> codeType
  multiplicity : Nat
  fiber_card_le : forall b, b ∈ Finset.univ.image code ->
    (Finset.univ.filter fun a => code a = b).card <= multiplicity

namespace BoundedCollisionCode

variable (C : BoundedCollisionCode (occurrence := occurrence)
  (codeType := codeType))

/-- The finite set of occupied collision cells. -/
abbrev Cell := {b // b ∈ Finset.univ.image C.code}

/-- Choose one honest occurrence from each occupied collision cell. -/
def representative (b : C.Cell) : occurrence :=
  Classical.choose (Finset.mem_image.mp b.2)

theorem representative_mem_univ (b : C.Cell) :
    C.representative b ∈ (Finset.univ : Finset occurrence) :=
  (Classical.choose_spec (Finset.mem_image.mp b.2)).1

@[simp] theorem code_representative (b : C.Cell) :
    C.code (C.representative b) = b.1 :=
  (Classical.choose_spec (Finset.mem_image.mp b.2)).2

/-- Representatives of different occupied cells are different. -/
theorem representative_injective : Function.Injective C.representative := by
  intro b c hbc
  apply Subtype.ext
  rw [← C.code_representative b, ← C.code_representative c, hbc]

/-- Every occurrence is covered by its occupied collision cell. -/
theorem exists_cell_code_eq (a : occurrence) :
    exists b : C.Cell, C.code a = b.1 := by
  exact ⟨⟨C.code a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩, rfl⟩

/-- Exact bounded-fibre count: `#occurrences ≤ M * #occupied cells`. -/
theorem card_le_multiplicity_mul_card_cell :
    Fintype.card occurrence <= C.multiplicity * Fintype.card C.Cell := by
  classical
  rw [Fintype.card, Finset.card_eq_sum_card_image C.code Finset.univ,
    Fintype.card_coe]
  calc
    (∑ b ∈ Finset.univ.image C.code,
        (Finset.univ.filter fun a => C.code a = b).card) <=
      ∑ _b ∈ Finset.univ.image C.code, C.multiplicity := by
        exact Finset.sum_le_sum fun b hb => C.fiber_card_le b hb
    _ = C.multiplicity * (Finset.univ.image C.code).card := by
      simp [Nat.mul_comm]

/-- If different collision codes imply a desired separation relation, the
chosen refinement is pairwise separated for that relation. -/
theorem pairwise_representative
    (separated : occurrence -> occurrence -> Prop)
    (hseparated : forall a b, C.code a ≠ C.code b -> separated a b) :
    Set.Pairwise (Set.univ : Set C.Cell) fun b c =>
      separated (C.representative b) (C.representative c) := by
  intro b _hb c _hc hbc
  apply hseparated
  intro hcode
  apply hbc
  apply Subtype.ext
  simpa using hcode

/-- Specialization to exact deduplication by a finite-valued map. -/
theorem card_le_multiplicity_mul_card_image
    {target : Type*} [DecidableEq target]
    (f : occurrence -> target) (M : Nat)
    (hfiber : forall y, y ∈ Finset.univ.image f ->
      (Finset.univ.filter fun a => f a = y).card <= M) :
    Fintype.card occurrence <= M * (Finset.univ.image f).card := by
  let D : BoundedCollisionCode (occurrence := occurrence)
      (codeType := target) := {
    code := f
    multiplicity := M
    fiber_card_le := hfiber }
  simpa [D, Fintype.card_coe] using D.card_le_multiplicity_mul_card_cell

#print axioms representative_injective
#print axioms exists_cell_code_eq
#print axioms card_le_multiplicity_mul_card_cell
#print axioms pairwise_representative
#print axioms card_le_multiplicity_mul_card_image

end BoundedCollisionCode

end
end FamilyStickyRandomFiniteCollisionRefinementV1
