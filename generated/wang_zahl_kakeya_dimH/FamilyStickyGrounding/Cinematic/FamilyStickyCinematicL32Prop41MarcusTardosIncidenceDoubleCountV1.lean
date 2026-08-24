import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1
import Mathlib.Data.Finset.Prod

set_option autoImplicit false
set_option maxRecDepth 10000

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosIncidenceDoubleCountV1

open FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1

noncomputable section

/-!
# Exact incidence double counting for Marcus--Tardos Lemma 3

For a finite list family `A`, `symbolDegree A a` counts the lists containing
`a`, while `orderedIntersectionSum A` sums `#(A_i ∩ A_j)` over ordered
distinct pairs.  The central identity is

`p + Σ_a d_a = Σ_a d_a^2`.

Together with the numerical Cauchy--Schwarz module this proves both lower
bounds stated in Marcus--Tardos Lemma 3.  No cyclic-order estimate is used.
-/

/-- Number of sets in the family which contain a symbol. -/
def symbolDegree {index symbol : Type*} [Fintype index]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) (a : symbol) : Nat :=
  ((Finset.univ : Finset index).filter fun i => a ∈ A i).card

/-- Sum of intersection sizes over ordered pairs of distinct indices. -/
def orderedIntersectionSum {index symbol : Type*} [Fintype index]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) : Nat :=
  ∑ ij ∈ orderedDistinctPairs index,
    (A ij.1 ∩ A ij.2).card

/-- Counting the same membership incidences first by symbol and then by
set gives the total-degree identity. -/
theorem sum_symbolDegree_eq_sum_card
    {index symbol : Type*} [Fintype index] [Fintype symbol]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) :
    ∑ a, symbolDegree A a = ∑ i, (A i).card := by
  classical
  simp only [symbolDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp

/-- Reindexing the intersection sum by symbols identifies its summand with
the off-diagonal of the corresponding symbol fibre. -/
theorem orderedIntersectionSum_eq_sum_degreeOffDiag_card
    {index symbol : Type*} [Fintype index] [Fintype symbol]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) :
    orderedIntersectionSum A =
      ∑ a, (((Finset.univ : Finset index).filter
        fun i => a ∈ A i).offDiag).card := by
  classical
  simp only [orderedIntersectionSum, orderedDistinctPairs]
  have hinner : ∀ ij : index × index,
      (A ij.1 ∩ A ij.2).card =
        ∑ a : symbol, if a ∈ A ij.1 ∩ A ij.2 then 1 else 0 := by
    intro ij
    rw [Finset.card_eq_sum_ones]
    symm
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  congr 1
  ext ij
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
    Finset.mem_inter, true_and]
  aesop

/-- Exact off-diagonal intersection double count. -/
theorem orderedIntersectionSum_eq_sum_degree_mul_pred
    {index symbol : Type*} [Fintype index] [Fintype symbol]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) :
    orderedIntersectionSum A =
      ∑ a, (symbolDegree A a * symbolDegree A a - symbolDegree A a) := by
  rw [orderedIntersectionSum_eq_sum_degreeOffDiag_card]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.offDiag_card]
  rfl

/-- Subtraction-free form of the preceding identity. -/
theorem orderedIntersectionSum_add_totalDegree_eq_sum_sq
    {index symbol : Type*} [Fintype index] [Fintype symbol]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) :
    orderedIntersectionSum A + ∑ a, symbolDegree A a =
      ∑ a, symbolDegree A a * symbolDegree A a := by
  rw [orderedIntersectionSum_eq_sum_degree_mul_pred]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  obtain h | h := Nat.eq_zero_or_pos (symbolDegree A a)
  · simp [h]
  · exact Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ h)

/-- A uniform `d`-element family has total degree `d*m`. -/
theorem sum_symbolDegree_eq_uniform_card_mul
    {index symbol : Type*} [Fintype index] [Fintype symbol]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) (d : Nat)
    (huniform : ∀ i, (A i).card = d) :
    ∑ a, symbolDegree A a = d * Fintype.card index := by
  rw [sum_symbolDegree_eq_sum_card]
  simp_rw [huniform]
  simp [mul_comm]

/-- First conclusion of Marcus--Tardos Lemma 3.  The strict source
hypothesis `d*m > 2*n` is retained; the conclusion is over `Real` to avoid
Nat-division truncation. -/
theorem uniform_orderedIntersectionSum_lower
    {index symbol : Type*} [Fintype index] [Fintype symbol]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) (d : Nat)
    (huniform : ∀ i, (A i).card = d)
    (hsymbol : 0 < Fintype.card symbol)
    (hlarge : 2 * Fintype.card symbol < d * Fintype.card index) :
    ((d * Fintype.card index : Nat) : Real) ^ 2 /
        (2 * (Fintype.card symbol : Real)) ≤
      (orderedIntersectionSum A : Real) := by
  have htotalNat := sum_symbolDegree_eq_uniform_card_mul A d huniform
  have hlargeReal : 2 * (Fintype.card symbol : Real) ≤
      ∑ a, (symbolDegree A a : Real) := by
    rw [← Nat.cast_sum, htotalNat]
    exact_mod_cast (Nat.le_of_lt hlarge)
  have hcollision := natDegree_collisionMass_lower
    (symbolDegree A) hsymbol hlargeReal
  have hidNat := orderedIntersectionSum_add_totalDegree_eq_sum_sq A
  have hidReal : (orderedIntersectionSum A : Real) +
      ∑ a, (symbolDegree A a : Real) =
        ∑ a, (symbolDegree A a : Real) ^ 2 := by
    norm_cast
    simpa [pow_two] using hidNat
  have htotalReal : (∑ a, (symbolDegree A a : Real)) =
      ((d * Fintype.card index : Nat) : Real) := by
    rw [← Nat.cast_sum, htotalNat]
  calc
    ((d * Fintype.card index : Nat) : Real) ^ 2 /
        (2 * (Fintype.card symbol : Real)) =
      (∑ a, (symbolDegree A a : Real)) ^ 2 /
        (2 * (Fintype.card symbol : Real)) := by rw [htotalReal]
    _ ≤ (∑ a, (symbolDegree A a : Real) ^ 2) -
        ∑ a, (symbolDegree A a : Real) := hcollision
    _ = (orderedIntersectionSum A : Real) := by linarith

/-- Second conclusion of Marcus--Tardos Lemma 3, again in the
denominator-free form valid even for an empty index type. -/
theorem orderedIntersectionSum_sq_le_index_card_sq_mul_sum_intersection_sq
    {index symbol : Type*} [Fintype index]
    [DecidableEq index] [DecidableEq symbol]
    (A : index → Finset symbol) :
    (orderedIntersectionSum A : Real) ^ 2 ≤
      (Fintype.card index : Real) ^ 2 *
        ∑ ij ∈ orderedDistinctPairs index,
          ((A ij.1 ∩ A ij.2).card : Real) ^ 2 := by
  have h := square_sum_le_index_card_sq_mul_sum_square
    (index := index)
    (fun ij => ((A ij.1 ∩ A ij.2).card : Real))
  simpa [orderedIntersectionSum, orderedDistinctPairs, Nat.cast_sum] using h

#print axioms symbolDegree
#print axioms orderedIntersectionSum
#print axioms sum_symbolDegree_eq_sum_card
#print axioms orderedIntersectionSum_eq_sum_degree_mul_pred
#print axioms orderedIntersectionSum_add_totalDegree_eq_sum_sq
#print axioms sum_symbolDegree_eq_uniform_card_mul
#print axioms uniform_orderedIntersectionSum_lower
#print axioms orderedIntersectionSum_sq_le_index_card_sq_mul_sum_intersection_sq

end

end FamilyStickyCinematicL32Prop41MarcusTardosIncidenceDoubleCountV1
