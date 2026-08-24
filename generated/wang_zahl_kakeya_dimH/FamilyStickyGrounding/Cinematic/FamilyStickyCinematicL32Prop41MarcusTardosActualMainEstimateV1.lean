import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualWeightedScoreIdentityV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveUpperCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFourCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosIncidenceDoubleCountV1
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualMainEstimateV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1
open FamilyStickyCinematicL32Prop41MarcusTardosIncidenceDoubleCountV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFourCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveUpperCleanV1
open FamilyStickyCinematicL32Prop41MarcusTardosActualWeightedScoreIdentityV1

/-!
# Actual Marcus--Tardos main quadratic estimate

This is the finite algebraic connector between the actual Lemma 4 score and
the pairwise Lemma 5 upper bound.  The quadratic estimate is proved here and
is not supplied as a premise.
-/

theorem sum_commonOrder_length_eq_orderedIntersectionSum
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol] [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol) :
    (∑ ij ∈ orderedDistinctPairs index,
      ((family ij.1).commonOrder (family ij.2)).length : Real) =
      (orderedIntersectionSum (fun i => (family i).support) : Real) := by
  rw [orderedIntersectionSum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [commonOrder_length]

theorem sum_commonOrder_length_sq_eq_intersection_sq
    {index symbol : Type*} [Fintype index] [DecidableEq index]
    [Fintype symbol] [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol) :
    (∑ ij ∈ orderedDistinctPairs index,
      (((family ij.1).commonOrder (family ij.2)).length : Real) ^ 2) =
      ∑ ij ∈ orderedDistinctPairs index,
        (((family ij.1).support ∩ (family ij.2).support).card : Real) ^ 2 := by
  apply Finset.sum_congr rfl
  intro ij hij
  rw [commonOrder_length]

theorem actual_family_main_inequality
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (depth : Nat) (hdepth : 1 ≤ depth)
    (d : Nat) (huniform : ∀ i, (family i).order.length = d)
    (hdpow : d ≤ 2 ^ depth)
    (weight : Fin depth → Real) (hweight : ∀ level, 0 < weight level) :
    -((Fintype.card index : Real) * (d : Real) ^ 2 *
        ∑ level : Fin depth,
          weight level / (2 : Real) ^ (level.1 + 1)) ≤
      (orderedIntersectionSum (fun i => (family i).support) : Real) *
          (∑ level, weight level) -
        (orderedIntersectionSum (fun i => (family i).support) : Real) ^ 2 /
          (4 * (Fintype.card index : Real) ^ 2 *
            ∑ level, (weight level)⁻¹) := by
  classical
  let p : Real :=
    (orderedIntersectionSum (fun i => (family i).support) : Real)
  let W : Real := ∑ level, weight level
  let V : Real := ∑ level, (weight level)⁻¹
  let M : Real := Fintype.card index
  let S : Real := ∑ ij ∈ orderedDistinctPairs index,
    (((family ij.1).commonOrder (family ij.2)).length : Real) ^ 2
  have hV : 0 < V := sum_weight_inv_pos hdepth weight hweight
  have hMcard : (0 : Real) < (Fintype.card index : Real) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card index)
  have hM : 0 < M := by simpa [M] using hMcard
  have hlenPow : ∀ i, (family i).order.length ≤ 2 ^ depth := by
    intro i
    rw [huniform i]
    exact hdpow
  have hlenD : ∀ i, (family i).order.length ≤ d := by
    intro i
    rw [huniform i]
  have hpairUpper : ∀ ij ∈ orderedDistinctPairs index,
      actualDyadicPairScore family weight ij.1 ij.2 ≤
        (((family ij.1).commonOrder (family ij.2)).length : Real) * W -
          (((family ij.1).commonOrder (family ij.2)).length : Real) ^ 2 /
            (4 * V) := by
    intro ij hij
    have hijne : ij.1 ≠ ij.2 := by
      simpa [orderedDistinctPairs] using hij
    let hir := hreverse hijne
    calc
      actualDyadicPairScore family weight ij.1 ij.2 =
          FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1.totalWeightedQ
            weight
            (FamilyStickyCinematicL32Prop41MarcusTardosActualLemmaFiveFinalV1.actualLevelQ
              (family ij.1) (family ij.2) hir) :=
        actualDyadicPairScore_eq_totalWeightedQ family weight ij.1 ij.2 hir
      _ ≤ (((family ij.1).commonOrder (family ij.2)).length : Real) * W -
          (((family ij.1).commonOrder (family ij.2)).length : Real) ^ 2 /
            (4 * V) := by
        simpa [W, V] using
          (actualLemmaFive_quotient depth hdepth
            (family ij.1) (family ij.2) hir (hlenPow ij.1) weight hweight)
  have hupperRaw :
      (∑ ij ∈ orderedDistinctPairs index,
        actualDyadicPairScore family weight ij.1 ij.2) ≤ p * W - S / (4 * V) := by
    calc
      (∑ ij ∈ orderedDistinctPairs index,
        actualDyadicPairScore family weight ij.1 ij.2) ≤
          ∑ ij ∈ orderedDistinctPairs index,
            ((((family ij.1).commonOrder (family ij.2)).length : Real) * W -
              (((family ij.1).commonOrder (family ij.2)).length : Real) ^ 2 /
                (4 * V)) :=
        Finset.sum_le_sum fun ij hij => hpairUpper ij hij
      _ = p * W - S / (4 * V) := by
        rw [Finset.sum_sub_distrib, Finset.sum_div]
        rw [← Finset.sum_mul]
        rw [sum_commonOrder_length_eq_orderedIntersectionSum family]
  have hCS :=
    orderedIntersectionSum_sq_le_index_card_sq_mul_sum_intersection_sq
      (fun i => (family i).support)
  have hS : S = ∑ ij ∈ orderedDistinctPairs index,
      (((family ij.1).support ∩ (family ij.2).support).card : Real) ^ 2 := by
    exact sum_commonOrder_length_sq_eq_intersection_sq family
  have hCS' : p ^ 2 ≤ M ^ 2 * S := by
    simpa [p, M, hS] using hCS
  have hfrac : p ^ 2 / (4 * M ^ 2 * V) ≤ S / (4 * V) := by
    have hden : 0 < 4 * M ^ 2 * V := by positivity
    rw [div_le_iff₀ hden]
    calc
      p ^ 2 ≤ M ^ 2 * S := hCS'
      _ = (S / (4 * V)) * (4 * M ^ 2 * V) := by
        field_simp [ne_of_gt hV]
  have hlower := actualLemmaFour family weight (fun l => (hweight l).le) hlenD
  calc
    -((Fintype.card index : Real) * (d : Real) ^ 2 *
        ∑ level : Fin depth,
          weight level / (2 : Real) ^ (level.1 + 1)) ≤
        ∑ ij ∈ orderedDistinctPairs index,
          actualDyadicPairScore family weight ij.1 ij.2 := by
      simpa using hlower
    _ ≤ p * W - S / (4 * V) := hupperRaw
    _ ≤ p * W - p ^ 2 / (4 * M ^ 2 * V) := by linarith
    _ = (orderedIntersectionSum (fun i => (family i).support) : Real) *
          (∑ level, weight level) -
        (orderedIntersectionSum (fun i => (family i).support) : Real) ^ 2 /
          (4 * (Fintype.card index : Real) ^ 2 *
            ∑ level, (weight level)⁻¹) := by rfl

#print axioms sum_commonOrder_length_eq_orderedIntersectionSum
#print axioms sum_commonOrder_length_sq_eq_intersection_sq
#print axioms actual_family_main_inequality

end FamilyStickyCinematicL32Prop41MarcusTardosActualMainEstimateV1
