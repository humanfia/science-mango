import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CardinalCWARestrictionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Def212ConvexWolffAtEveryScaleV2

noncomputable section

/-!
# Cardinal-normalized CWA under finite restriction

Restricting a family can increase its cardinal-normalized concentration only
by the reciprocal retained-cardinality fraction.  This module records the
exact finite statement used after either a doubled-parent or conflict-graph
greedy extraction.
-/

/-- Convex family obtained by retaining the indices in `selected`. -/
def restrictConvexFamily
    {index : Type*} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (selected : Finset index) :
    ConvexFamily {i // i ∈ selected} :=
  fun i ↦ F i.1

@[simp]
theorem restrictConvexFamily_apply
    {index : Type*} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (selected : Finset index)
    (i : {i // i ∈ selected}) :
    restrictConvexFamily F selected i = F i.1 := rfl

/-- The number of retained members captured by a convex body is at most the
number captured in the source family. -/
theorem containedIndices_restrict_card_le
    {index : Type*} [Fintype index] [DecidableEq index]
    (F : ConvexFamily index) (selected : Finset index)
    (K : ConvexBody Space) :
    (containedIndices (restrictConvexFamily F selected) K).card ≤
      (containedIndices F K).card := by
  classical
  let inclusion : {i // i ∈ selected} ↪ index :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hsubset :
      (containedIndices (restrictConvexFamily F selected) K).map inclusion ⊆
        containedIndices F K := by
    intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    rw [mem_containedIndices] at hj ⊢
    exact hj
  rw [← Finset.card_map inclusion]
  exact Finset.card_le_card hsubset

/-- If the source cardinal is at most `B` times the retained cardinal, then
restriction preserves the Convex Wolff axioms with the exact loss `B`. -/
theorem satisfiesConvexWolffAxioms_restrict
    {index : Type*} [Fintype index] [DecidableEq index]
    {F : ConvexFamily index} {selected : Finset index}
    {C B : ENNReal}
    (hCWA : SatisfiesConvexWolffAxioms C F)
    (hcard : (Fintype.card index : ENNReal) ≤
      B * (selected.card : ENNReal)) :
    SatisfiesConvexWolffAxioms (B * C)
      (restrictConvexFamily F selected) := by
  intro K
  have hcaptured :
      ((containedIndices (restrictConvexFamily F selected) K).card : ENNReal) ≤
        ((containedIndices F K).card : ENNReal) := by
    exact_mod_cast containedIndices_restrict_card_le F selected K
  calc
    ((containedIndices (restrictConvexFamily F selected) K).card : ENNReal) ≤
        ((containedIndices F K).card : ENNReal) := hcaptured
    _ ≤ C * volume (K : Set Space) *
        (Fintype.card index : ENNReal) := hCWA K
    _ ≤ C * volume (K : Set Space) *
        (B * (selected.card : ENNReal)) := by
      gcongr
    _ = (B * C) * volume (K : Set Space) *
        (Fintype.card {i // i ∈ selected} : ENNReal) := by
      simp only [Fintype.card_coe]
      ring

#print axioms restrictConvexFamily_apply
#print axioms containedIndices_restrict_card_le
#print axioms satisfiesConvexWolffAxioms_restrict

end
end Family8CardinalCWARestrictionV1
