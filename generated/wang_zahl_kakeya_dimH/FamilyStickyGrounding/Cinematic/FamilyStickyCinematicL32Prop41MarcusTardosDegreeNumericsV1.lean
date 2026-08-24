import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1

noncomputable section

/-!
# Numerical core of Marcus--Tardos Lemma 3

The proof of the intersection-reverse sequence theorem first performs two
finite Cauchy--Schwarz estimates.  This module freezes their denominator-free
forms.  They are independent of cyclic order and do not contain the final
Marcus--Tardos growth bound.
-/

/-- If the total degree is at least twice the alphabet size, the sum of
`degree^2 - degree` has the lower bound used in Marcus--Tardos Lemma 3. -/
theorem collisionMass_lower_of_two_card_le_total
    {symbol : Type*} [Fintype symbol]
    (degree : symbol → Real)
    (hdegree : ∀ a, 0 ≤ degree a)
    (hcard : 0 < Fintype.card symbol)
    (hlarge : 2 * (Fintype.card symbol : Real) ≤ ∑ a, degree a) :
    (∑ a, degree a) ^ 2 /
        (2 * (Fintype.card symbol : Real)) ≤
      (∑ a, (degree a) ^ 2) - ∑ a, degree a := by
  let total : Real := ∑ a, degree a
  let squares : Real := ∑ a, (degree a) ^ 2
  have htotal : 0 ≤ total := by
    exact Finset.sum_nonneg fun a _ => hdegree a
  have hCS : total ^ 2 ≤ (Fintype.card symbol : Real) * squares := by
    simpa only [total, squares, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset symbol)) (f := degree))
  have hlarge' : 2 * (Fintype.card symbol : Real) ≤ total := by
    simpa only [total] using hlarge
  have hdenom : 0 < 2 * (Fintype.card symbol : Real) := by
    positivity
  rw [div_le_iff₀ hdenom]
  change total ^ 2 ≤ (squares - total) *
    (2 * (Fintype.card symbol : Real))
  nlinarith

/-- Nat-valued degree specialization, in the exact form needed after finite
incidence double counting. -/
theorem natDegree_collisionMass_lower
    {symbol : Type*} [Fintype symbol]
    (degree : symbol → Nat)
    (hcard : 0 < Fintype.card symbol)
    (hlarge : 2 * (Fintype.card symbol : Real) ≤
      ∑ a, (degree a : Real)) :
    (∑ a, (degree a : Real)) ^ 2 /
        (2 * (Fintype.card symbol : Real)) ≤
      (∑ a, (degree a : Real) ^ 2) -
        ∑ a, (degree a : Real) := by
  exact collisionMass_lower_of_two_card_le_total
    (fun a => (degree a : Real)) (fun _ => Nat.cast_nonneg _) hcard hlarge

/-- Ordered pairs of distinct list indices, matching the paper's convention
that every unordered pair is counted twice. -/
def orderedDistinctPairs (index : Type*) [Fintype index]
    [DecidableEq index] : Finset (index × index) :=
  (Finset.univ : Finset index).offDiag

theorem card_orderedDistinctPairs_le_sq
    (index : Type*) [Fintype index] [DecidableEq index] :
    (orderedDistinctPairs index).card ≤ (Fintype.card index) ^ 2 := by
  calc
    (orderedDistinctPairs index).card ≤
        (Finset.univ : Finset (index × index)).card :=
      Finset.card_le_card (by simp [orderedDistinctPairs])
    _ = (Fintype.card index) ^ 2 := by simp [pow_two]

/-- Second Cauchy--Schwarz estimate of Marcus--Tardos Lemma 3, written
without division so the zero-index case is honest. -/
theorem square_sum_le_index_card_sq_mul_sum_square
    {index : Type*} [Fintype index] [DecidableEq index]
    (intersectionSize : index × index → Real) :
    (∑ ij ∈ orderedDistinctPairs index, intersectionSize ij) ^ 2 ≤
      (Fintype.card index : Real) ^ 2 *
        ∑ ij ∈ orderedDistinctPairs index, (intersectionSize ij) ^ 2 := by
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := orderedDistinctPairs index) (f := intersectionSize)
  calc
    (∑ ij ∈ orderedDistinctPairs index, intersectionSize ij) ^ 2 ≤
        ((orderedDistinctPairs index).card : Real) *
          ∑ ij ∈ orderedDistinctPairs index,
            (intersectionSize ij) ^ 2 := by
      exact_mod_cast hCS
    _ ≤ (Fintype.card index : Real) ^ 2 *
        ∑ ij ∈ orderedDistinctPairs index,
          (intersectionSize ij) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_orderedDistinctPairs_le_sq index
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _

#print axioms collisionMass_lower_of_two_card_le_total
#print axioms natDegree_collisionMass_lower
#print axioms orderedDistinctPairs
#print axioms card_orderedDistinctPairs_le_sq
#print axioms square_sum_le_index_card_sq_mul_sum_square

end

end FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1
