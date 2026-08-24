import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosPerfectSquareV1
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFourCleanV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1
open FamilyStickyCinematicL32Prop41MarcusTardosPerfectSquareV1

/-!
# Fully finite actual Marcus--Tardos Lemma 4

For each level and ordered symbol pair, the feature is the actual dyadic
order sign from `DyadicActualPairTermV1`.  Thus the all-list Gram sum is a
perfect square.  Its diagonal is produced by the literal recursive blocks,
giving the paper's explicit `m d² ∑_l w_l / 2^(l+1)` loss.
-/

noncomputable def actualDyadicPairScore
    {index symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    {depth : Nat} (family : index → DistinctCyclicSequence symbol)
    (weight : Fin depth → Real) (i j : index) : Real :=
  ∑ level : Fin depth, ∑ p : symbol × symbol,
    weight level *
      dyadicOrderTerm (level.1 + 1) (family i) p *
      dyadicOrderTerm (level.1 + 1) (family j) p

theorem one_list_weighted_diagonal_le
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    {depth d : Nat} (A : DistinctCyclicSequence symbol)
    (weight : Fin depth → Real) (hweight : ∀ level, 0 ≤ weight level)
    (hlength : A.order.length ≤ d) :
    (∑ q : Fin depth × (symbol × symbol),
      weight q.1 * dyadicOrderTerm (q.1.1 + 1) A q.2 ^ 2) ≤
      (d : Real) ^ 2 *
        ∑ level : Fin depth, weight level / (2 : Real) ^ (level.1 + 1) := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ level : Fin depth, ∑ p : symbol × symbol,
        weight level * dyadicOrderTerm (level.1 + 1) A p ^ 2) ≤
        ∑ level : Fin depth,
          (d : Real) ^ 2 *
            (weight level / (2 : Real) ^ (level.1 + 1)) := by
      apply Finset.sum_le_sum
      intro level _
      rw [← Finset.mul_sum]
      have hdiag := sum_dyadicOrderTerm_sq_le_sq_div_pow
        (level.1 + 1) A
      have hlenReal : (A.order.length : Real) ≤ (d : Real) := by
        exact_mod_cast hlength
      have hsq : (A.order.length : Real) ^ 2 ≤ (d : Real) ^ 2 := by
        have hleft : 0 ≤ (A.order.length : Real) := by positivity
        have hright : 0 ≤ (d : Real) := by positivity
        nlinarith
      have hdiv :
          (A.order.length : Real) ^ 2 / (2 : Real) ^ (level.1 + 1) ≤
            (d : Real) ^ 2 / (2 : Real) ^ (level.1 + 1) := by
        exact div_le_div_of_nonneg_right hsq (by positivity)
      calc
        weight level *
            (∑ p : symbol × symbol,
              dyadicOrderTerm (level.1 + 1) A p ^ 2) ≤
            weight level *
              ((A.order.length : Real) ^ 2 /
                (2 : Real) ^ (level.1 + 1)) :=
          mul_le_mul_of_nonneg_left hdiag (hweight level)
        _ ≤ weight level *
              ((d : Real) ^ 2 / (2 : Real) ^ (level.1 + 1)) :=
          mul_le_mul_of_nonneg_left hdiv (hweight level)
        _ = (d : Real) ^ 2 *
              (weight level / (2 : Real) ^ (level.1 + 1)) := by ring
    _ = (d : Real) ^ 2 *
        ∑ level : Fin depth, weight level / (2 : Real) ^ (level.1 + 1) := by
      rw [Finset.mul_sum]

theorem family_weighted_diagonal_le
    {index symbol : Type*} [Fintype index] [Fintype symbol]
    [DecidableEq symbol]
    {depth d : Nat} (family : index → DistinctCyclicSequence symbol)
    (weight : Fin depth → Real) (hweight : ∀ level, 0 ≤ weight level)
    (hlength : ∀ i, (family i).order.length ≤ d) :
    (∑ i : index, ∑ q : Fin depth × (symbol × symbol),
      weight q.1 *
        dyadicOrderTerm (q.1.1 + 1) (family i) q.2 ^ 2) ≤
      (Fintype.card index : Real) * (d : Real) ^ 2 *
        ∑ level : Fin depth,
          weight level / (2 : Real) ^ (level.1 + 1) := by
  calc
    (∑ i : index, ∑ q : Fin depth × (symbol × symbol),
        weight q.1 *
          dyadicOrderTerm (q.1.1 + 1) (family i) q.2 ^ 2) ≤
        ∑ _i : index, (d : Real) ^ 2 *
          ∑ level : Fin depth,
            weight level / (2 : Real) ^ (level.1 + 1) := by
      exact Finset.sum_le_sum fun i _ ↦
        one_list_weighted_diagonal_le (family i) weight hweight (hlength i)
    _ = (Fintype.card index : Real) * (d : Real) ^ 2 *
        ∑ level : Fin depth,
          weight level / (2 : Real) ^ (level.1 + 1) := by
      simp
      ring

/-- Marcus--Tardos Lemma 4 with the actual finite dyadic sign features and
the paper's explicit constant one in the diagonal loss. -/
theorem actualLemmaFour
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol] [DecidableEq symbol]
    {depth d : Nat} (family : index → DistinctCyclicSequence symbol)
    (weight : Fin depth → Real) (hweight : ∀ level, 0 ≤ weight level)
    (hlength : ∀ i, (family i).order.length ≤ d) :
    -((Fintype.card index : Real) * (d : Real) ^ 2 *
        ∑ level : Fin depth,
          weight level / (2 : Real) ^ (level.1 + 1)) ≤
      ∑ ij ∈ orderedDistinctPairs index,
        actualDyadicPairScore family weight ij.1 ij.2 := by
  have h := weighted_offDiag_ge_neg_budget
    (fun q : Fin depth × (symbol × symbol) ↦ weight q.1)
    (fun i q ↦ dyadicOrderTerm (q.1.1 + 1) (family i) q.2)
    ((Fintype.card index : Real) * (d : Real) ^ 2 *
      ∑ level : Fin depth,
        weight level / (2 : Real) ^ (level.1 + 1))
    (fun q ↦ hweight q.1)
    (family_weighted_diagonal_le family weight hweight hlength)
  simpa only [actualDyadicPairScore, Fintype.sum_prod_type] using h

#print axioms actualDyadicPairScore
#print axioms one_list_weighted_diagonal_le
#print axioms family_weighted_diagonal_le
#print axioms actualLemmaFour

end FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFourCleanV1
