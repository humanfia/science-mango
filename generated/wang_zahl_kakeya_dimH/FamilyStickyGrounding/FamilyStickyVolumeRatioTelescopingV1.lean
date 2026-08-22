import FamilyStickyGrounding.FamilyStickyAdjacentNormalizedCrossV1

open scoped BigOperators ENNReal

namespace FamilyStickyVolumeRatioTelescopingV1

noncomputable section

/-!
# Sticky Kakeya: finite volume-ratio telescoping

The adjacent geometric estimate naturally retains ratios of successive test
body and tube volumes.  This module proves the exact finite cancellation used
in the source proof.  Positivity and finiteness are explicit because division
in `ENNReal` cannot cancel zero or infinity.
-/

/-- Forward adjacent ratios telescope exactly. -/
theorem prod_forward_adjacent_ratio
    (depth : Nat) (a : Nat → ENNReal)
    (ha0 : ∀ m, m ≤ depth → a m ≠ 0)
    (haTop : ∀ m, m ≤ depth → a m ≠ ∞) :
    (∏ m ∈ Finset.range depth, a (m + 1) / a m) =
      a depth / a 0 := by
  induction depth with
  | zero => simp [ENNReal.div_self (ha0 0 le_rfl) (haTop 0 le_rfl)]
  | succ n ih =>
      have ha0' : ∀ m, m ≤ n → a m ≠ 0 := fun m hm =>
        ha0 m (hm.trans (Nat.le_succ n))
      have haTop' : ∀ m, m ≤ n → a m ≠ ∞ := fun m hm =>
        haTop m (hm.trans (Nat.le_succ n))
      rw [Finset.prod_range_succ, ih ha0' haTop']
      calc
        a n / a 0 * (a (n + 1) / a n) =
            (a n / a n) * (a (n + 1) / a 0) := by
          simp only [div_eq_mul_inv]
          ring
        _ = a (n + 1) / a 0 := by
          rw [ENNReal.div_self (ha0 n (Nat.le_succ n))
            (haTop n (Nat.le_succ n)), one_mul]

/-- Reverse adjacent ratios telescope exactly. -/
theorem prod_reverse_adjacent_ratio
    (depth : Nat) (a : Nat → ENNReal)
    (ha0 : ∀ m, m ≤ depth → a m ≠ 0)
    (haTop : ∀ m, m ≤ depth → a m ≠ ∞) :
    (∏ m ∈ Finset.range depth, a m / a (m + 1)) =
      a 0 / a depth := by
  induction depth with
  | zero => simp [ENNReal.div_self (ha0 0 le_rfl) (haTop 0 le_rfl)]
  | succ n ih =>
      have ha0' : ∀ m, m ≤ n → a m ≠ 0 := fun m hm =>
        ha0 m (hm.trans (Nat.le_succ n))
      have haTop' : ∀ m, m ≤ n → a m ≠ ∞ := fun m hm =>
        haTop m (hm.trans (Nat.le_succ n))
      rw [Finset.prod_range_succ, ih ha0' haTop']
      calc
        a 0 / a n * (a n / a (n + 1)) =
            (a n / a n) * (a 0 / a (n + 1)) := by
          simp only [div_eq_mul_inv]
          ring
        _ = a 0 / a (n + 1) := by
          rw [ENNReal.div_self (ha0 n (Nat.le_succ n))
            (haTop n (Nat.le_succ n)), one_mul]

/-- The exact product from Lemma 7.2: test-body growth and tube-volume decay
separate, telescope, and leave only the two endpoint ratios. -/
theorem prod_bodyGrowth_mul_tubeDecay
    (depth : Nat) (bodyVolume tubeVolume : Nat → ENNReal)
    (hbody0 : ∀ m, m ≤ depth → bodyVolume m ≠ 0)
    (hbodyTop : ∀ m, m ≤ depth → bodyVolume m ≠ ∞)
    (htube0 : ∀ m, m ≤ depth → tubeVolume m ≠ 0)
    (htubeTop : ∀ m, m ≤ depth → tubeVolume m ≠ ∞) :
    (∏ m ∈ Finset.range depth,
        (bodyVolume (m + 1) / bodyVolume m) *
          (tubeVolume m / tubeVolume (m + 1))) =
      (bodyVolume depth / bodyVolume 0) *
        (tubeVolume 0 / tubeVolume depth) := by
  rw [Finset.prod_mul_distrib,
    prod_forward_adjacent_ratio depth bodyVolume hbody0 hbodyTop,
    prod_reverse_adjacent_ratio depth tubeVolume htube0 htubeTop]

#print axioms prod_forward_adjacent_ratio
#print axioms prod_reverse_adjacent_ratio
#print axioms prod_bodyGrowth_mul_tubeDecay

end
end FamilyStickyVolumeRatioTelescopingV1
