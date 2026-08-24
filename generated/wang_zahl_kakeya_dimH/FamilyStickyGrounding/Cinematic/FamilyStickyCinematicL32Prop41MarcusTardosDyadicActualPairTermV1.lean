import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDyadicWithinBlockPairCountV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicDiagonalV1
open FamilyStickyCinematicL32Prop41MarcusTardosDyadicWithinBlockPairCountV1
open FamilyStickyCinematicL32Prop41MarcusTardosTaggedSplitOrderSignV1

/-!
# Actual signed dyadic pair term and its diagonal

The paper's level term is the order sign of an ordered symbol pair when both
symbols lie in one actual dyadic block, and zero otherwise.  Its square is
therefore exactly the indicator of the finite same-block support.
-/

theorem rankSign_sq_of_ne
    {symbol : Type*} [DecidableEq symbol]
    (rank : symbol → Nat) {a b : symbol} (hab : a ≠ b) :
    rankSign rank a b ^ 2 = 1 := by
  simp only [rankSign, hab, if_false]
  split <;> norm_num

noncomputable def dyadicOrderTerm
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol)
    (p : symbol × symbol) : Real :=
  if p ∈ sameDyadicOrderedPairs depth A.order then
    rankSign (fun x ↦ A.order.idxOf x) p.1 p.2
  else 0

theorem dyadicOrderTerm_sq
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol)
    (p : symbol × symbol) :
    dyadicOrderTerm depth A p ^ 2 =
      if p ∈ sameDyadicOrderedPairs depth A.order then 1 else 0 := by
  classical
  simp only [dyadicOrderTerm]
  split_ifs with hp
  · have hsame : SameDyadicOrderedPair depth A.order p := by
      simpa [sameDyadicOrderedPairs] using hp
    exact rankSign_sq_of_ne _ hsame.1
  · norm_num

theorem sum_dyadicOrderTerm_sq_eq_card
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol) :
    (∑ p : symbol × symbol, dyadicOrderTerm depth A p ^ 2) =
      ((sameDyadicOrderedPairs depth A.order).card : Real) := by
  classical
  simp_rw [dyadicOrderTerm_sq]
  simp

theorem cast_orderedPairCount
    (n : Nat) :
    (((n * (n - 1) : Nat) : Real)) =
      (n : Real) * ((n : Real) - 1) := by
  cases n with
  | zero => norm_num
  | succ n => simp

/-- The actual sign-square diagonal at one dyadic level is bounded by the
paper's `d²/2^level`, with `d` the literal list length. -/
theorem sum_dyadicOrderTerm_sq_le_sq_div_pow
    {symbol : Type*} [Fintype symbol] [DecidableEq symbol]
    (depth : Nat) (A : DistinctCyclicSequence symbol) :
    (∑ p : symbol × symbol, dyadicOrderTerm depth A p ^ 2) ≤
      (A.order.length : Real) ^ 2 / (2 : Real) ^ depth := by
  rw [sum_dyadicOrderTerm_sq_eq_card]
  have hcardNat := card_sameDyadicOrderedPairs_le_sum_block_orderedPairs
    depth A.order A.nodup_order
  have hcardReal :
      ((sameDyadicOrderedPairs depth A.order).card : Real) ≤
        ((∑ i : BlockIndex depth A.order,
          (blockAt depth A.order i).length *
            ((blockAt depth A.order i).length - 1) : Nat) : Real) := by
    exact_mod_cast hcardNat
  rw [Nat.cast_sum] at hcardReal
  simp_rw [cast_orderedPairCount] at hcardReal
  exact hcardReal.trans (sum_block_orderedPairs_le_sq_div_pow depth A.order)

#print axioms rankSign_sq_of_ne
#print axioms dyadicOrderTerm
#print axioms dyadicOrderTerm_sq
#print axioms sum_dyadicOrderTerm_sq_eq_card
#print axioms cast_orderedPairCount
#print axioms sum_dyadicOrderTerm_sq_le_sq_div_pow

end FamilyStickyCinematicL32Prop41MarcusTardosDyadicActualPairTermV1
