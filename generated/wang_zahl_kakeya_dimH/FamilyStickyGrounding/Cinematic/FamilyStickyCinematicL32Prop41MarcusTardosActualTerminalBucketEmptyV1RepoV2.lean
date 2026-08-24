import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosActualBucketTelescopingCoverV1RepoV2
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FamilyStickyCinematicL32Prop41MarcusTardosActualTerminalBucketEmptyV1

open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosActualLongIndexCapV1

/-! At level `m`, the dyadic threshold already exceeds every list length. -/

theorem terminal_longIndex_empty
    {index symbol : Type*} [Fintype index] [Nonempty index]
    [DecidableEq index] [Fintype symbol] [Nonempty symbol]
    [DecidableEq symbol]
    (family : index → DistinctCyclicSequence symbol)
    (depth : Nat) :
    longIndex family depth (Fintype.card index) = ∅ := by
  classical
  let n : Real := Fintype.card symbol
  let m : Real := Fintype.card index
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card symbol)
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card index)
  have hmOne : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast
      (Nat.one_le_iff_ne_zero.2
        (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card index)))
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsqrtLeM : Real.sqrt m ≤ m := by
    rcases le_total (Real.sqrt m) 1 with hs | hs
    · exact hs.trans hmOne
    · have hmul := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg m)
      simpa [Real.mul_self_sqrt hm.le] using hmul
  have hmLePow : m ≤ (2 : Real) ^ Fintype.card index := by
    dsimp [m]
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hsqrtLePow : Real.sqrt m ≤
      (2 : Real) ^ Fintype.card index := hsqrtLeM.trans hmLePow
  have hterm : n ≤
      (2 : Real) ^ Fintype.card index * (21 * n / Real.sqrt m) := by
    calc
      n ≤ 21 * n := by nlinarith
      _ = (21 * n / Real.sqrt m) * Real.sqrt m := by
        field_simp [ne_of_gt hsm]
      _ ≤ (21 * n / Real.sqrt m) *
          (2 : Real) ^ Fintype.card index :=
        mul_le_mul_of_nonneg_left hsqrtLePow (by positivity)
      _ = (2 : Real) ^ Fintype.card index *
          (21 * n / Real.sqrt m) := by ring
  have hthreshold : n ≤
      paperThreshold depth (Fintype.card index) index symbol := by
    dsimp [paperThreshold, paperStep, n, m]
    have hb : 0 ≤ paperBaseline depth symbol := by
      dsimp [paperBaseline]
      positivity
    linarith
  apply Finset.Subset.antisymm ?_ (Finset.empty_subset _)
  intro i hi
  exfalso
  have hlong : paperThreshold depth (Fintype.card index) index symbol <
      ((family i).order.length : Real) :=
    (Finset.mem_filter.mp hi).2
  have hlenNat := sequence_length_le_symbol_card (family i)
  have hlen : ((family i).order.length : Real) ≤ n := by
    dsimp [n]
    exact_mod_cast hlenNat
  linarith

#print axioms terminal_longIndex_empty

end FamilyStickyCinematicL32Prop41MarcusTardosActualTerminalBucketEmptyV1
