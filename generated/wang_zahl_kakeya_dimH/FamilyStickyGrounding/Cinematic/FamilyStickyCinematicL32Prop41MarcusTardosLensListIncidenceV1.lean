import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1

open scoped BigOperators

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence

noncomputable section

/-!
# The finite lens-to-list incidence reduction in Marcus--Tardos Lemma 10

The proof of Marcus--Tardos Lemma 10 separates non-degenerate lenses into
three classes.  For each curve and each class it forms a cyclic neighbor
list.  A lens-face or inverse-face occurs in a list at each side; an oriented
moon-face occurs in the list belonging to its positive side.  Consequently
every lens has a distinct code which is either its underlying curve
(degenerate case) or an occurrence in one of the three list families.

This module formalizes exactly that finite incidence/cardinality reduction.
It neither assumes nor states the hard cyclic-list length estimate.
-/

/-- The three non-degenerate lens classes in Marcus--Tardos Lemma 10. -/
inductive ProperLensKind
  | lensFace
  | moonFace
  | inverseFace
  deriving DecidableEq

instance : Fintype ProperLensKind where
  elems := {ProperLensKind.lensFace, ProperLensKind.moonFace,
    ProperLensKind.inverseFace}
  complete k := by cases k <;> simp

/-- One occurrence of a neighbor symbol in one of the three curve-indexed
cyclic list families. -/
abbrev ListOccurrence {curve : Type*} [DecidableEq curve]
    (lists : ProperLensKind → curve → DistinctCyclicSequence curve) :=
  Σ k : ProperLensKind, Σ c : curve,
    {c' : curve // c' ∈ (lists k c).support}

/-- Exact cardinality of the occurrence type: it is the total length of all
three families of cyclic lists. -/
theorem card_listOccurrence
    {curve : Type*} [Fintype curve] [DecidableEq curve]
    (lists : ProperLensKind → curve → DistinctCyclicSequence curve) :
    Fintype.card (ListOccurrence lists) =
      ∑ k : ProperLensKind, ∑ c : curve, (lists k c).order.length := by
  simp only [ListOccurrence, Fintype.card_sigma, Fintype.card_coe]
  congr 1
  funext k
  congr 1
  funext c
  exact card_support (lists k c)

/-- The smallest faithful discrete output of the geometric part of Lemma 10.
The embedding records both the classification and the fact that different
lenses cannot collapse to the same chosen list occurrence. -/
structure LensListEncoding (curve lens : Type*)
    [Fintype curve] [DecidableEq curve] where
  lists : ProperLensKind → curve → DistinctCyclicSequence curve
  lensCode : lens ↪ Sum curve (ListOccurrence lists)

namespace LensListEncoding

variable {curve lens : Type*} [Fintype curve] [DecidableEq curve]

/-- The geometric five-pseudo-circle case analysis must establish this
property separately for each of the three list classes. -/
def ListsPairwiseIntersectionReverse (E : LensListEncoding curve lens) : Prop :=
  ∀ k, PairwiseIntersectionReverse (E.lists k)

/-- The elementary last line of Marcus--Tardos Lemma 10: the number of
lenses is at most the number of curves plus the total list length. -/
theorem card_lens_le_curve_add_sum_list_length
    [Fintype lens] (E : LensListEncoding curve lens) :
    Fintype.card lens ≤ Fintype.card curve +
      ∑ k : ProperLensKind, ∑ c : curve, (E.lists k c).order.length := by
  calc
    Fintype.card lens ≤
        Fintype.card (Sum curve (ListOccurrence E.lists)) :=
      Fintype.card_le_of_injective E.lensCode E.lensCode.injective
    _ = Fintype.card curve + Fintype.card (ListOccurrence E.lists) := by
      rw [Fintype.card_sum]
    _ = Fintype.card curve +
        ∑ k : ProperLensKind, ∑ c : curve,
          (E.lists k c).order.length := by
      rw [card_listOccurrence]

/-- Finset-facing form used by the rectangle-to-lens image: only the selected
lens subtype needs to embed into the MT occurrence carrier. -/
theorem card_finset_le_curve_add_sum_list_length
    [DecidableEq lens] (selected : Finset lens)
    (lists : ProperLensKind → curve → DistinctCyclicSequence curve)
    (encode : {L : lens // L ∈ selected} ↪
      Sum curve (ListOccurrence lists)) :
    selected.card ≤ Fintype.card curve +
      ∑ k : ProperLensKind, ∑ c : curve, (lists k c).order.length := by
  simpa only [Fintype.card_coe] using
    (card_lens_le_curve_add_sum_list_length
      (LensListEncoding.mk lists encode))

/-- Pairwise intersection reversal survives restriction to any injectively
indexed subfamily of curves. -/
theorem ListsPairwiseIntersectionReverse.comp_injective
    (E : LensListEncoding curve lens)
    (h : E.ListsPairwiseIntersectionReverse)
    {index : Type*} (f : index → curve) (hf : Function.Injective f) :
    ∀ k, PairwiseIntersectionReverse (E.lists k ∘ f) := by
  intro k
  exact (h k).comp_injective f hf

#print axioms card_listOccurrence
#print axioms ListsPairwiseIntersectionReverse
#print axioms card_lens_le_curve_add_sum_list_length
#print axioms card_finset_le_curve_add_sum_list_length
#print axioms ListsPairwiseIntersectionReverse.comp_injective

end LensListEncoding

end

end FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
