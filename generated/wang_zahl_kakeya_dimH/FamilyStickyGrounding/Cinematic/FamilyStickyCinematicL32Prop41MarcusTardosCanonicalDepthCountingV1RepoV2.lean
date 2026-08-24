import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosNonuniformExplicitV1RepoV2
import Mathlib.Data.Nat.Log

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosUniformPaperCountingV1
open FamilyStickyCinematicL32Prop41MarcusTardosNonuniformExplicitV1

def canonicalDepth (symbol : Type*) [Fintype symbol] : Nat :=
  Nat.log 2 (Fintype.card symbol) + 1

theorem one_le_canonicalDepth
    (symbol : Type*) [Fintype symbol] :
    1 ≤ canonicalDepth symbol := by
  simp [canonicalDepth]

theorem symbol_card_le_two_pow_canonicalDepth
    (symbol : Type*) [Fintype symbol] :
    Fintype.card symbol ≤ 2 ^ canonicalDepth symbol := by
  exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
    (Fintype.card symbol)).le

theorem uniform_counting_canonicalDepth
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family)
    (d : Nat) (huniform : ∀ i, (family i).order.length = d) :
    (d : Real) ≤ 8 * (canonicalDepth symbol : Real) *
        Real.sqrt (Fintype.card symbol : Real) ∨
      (d : Real) ≤ 21 * (Fintype.card symbol : Real) /
        Real.sqrt (Fintype.card index : Real) := by
  apply uniform_counting_eight_or_twentyone family hreverse
    (canonicalDepth symbol) (one_le_canonicalDepth symbol) d huniform
  calc
    d = (family (Classical.choice inferInstance)).order.length :=
      (huniform _).symm
    _ ≤ Fintype.card symbol :=
      FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1.sequence_length_le_symbol_card _
    _ ≤ 2 ^ canonicalDepth symbol :=
      symbol_card_le_two_pow_canonicalDepth symbol

theorem nonuniform_total_length_canonicalDepth
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (hreverse : PairwiseIntersectionReverse family) :
    (∑ i : index, ((family i).order.length : Real)) ≤
      16 * (canonicalDepth symbol : Real) * (Fintype.card index : Real) *
          Real.sqrt (Fintype.card symbol : Real) +
        105 * (Fintype.card symbol : Real) *
          Real.sqrt (Fintype.card index : Real) := by
  exact nonuniform_total_length_le_explicit family hreverse
    (canonicalDepth symbol) (one_le_canonicalDepth symbol)
    (symbol_card_le_two_pow_canonicalDepth symbol)

#print axioms symbol_card_le_two_pow_canonicalDepth
#print axioms uniform_counting_canonicalDepth
#print axioms nonuniform_total_length_canonicalDepth

end FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
