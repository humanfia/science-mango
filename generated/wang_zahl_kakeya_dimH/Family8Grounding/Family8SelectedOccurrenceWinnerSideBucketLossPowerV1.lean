import Family8Grounding.Family8GreedyWinnerAutomaticJohnSideBucketV1
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV10
import Mathlib.Tactic

/-!
# Power absorption for the selected-occurrence winner-side loss

The outer winner bucket uses the literal interval `[2 * delta, 576]`.
Its cubic dyadic loss is bounded by the already quantified selected-parent
logarithmic loss at `rho = delta`.  This is only a scalar adapter: no
occurrence, side label, or shading is selected here.
-/

open scoped ENNReal NNReal

namespace Family8SelectedOccurrenceWinnerSideBucketLossPowerV1

open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

set_option autoImplicit false
set_option warningAsError true

/-- The outer winner-side logarithmic loss is no larger than the existing
selected-parent logarithmic loss at the same source scale. -/
theorem winnerSideBucketLoss_le_selectedParentLogarithmicSideBucketLoss
    (delta : NNReal) (hdelta : 0 < delta) :
    winnerSideBucketLoss delta <=
      selectedParentLogarithmicSideBucketLoss delta := by
  have hdeltaReal : (0 : Real) < (delta : Real) := by
    exact_mod_cast hdelta
  have hlower : (0 : Real) < (((2 * delta : NNReal) : Real)) := by
    positivity
  have hratioPos :
      (0 : Real) < 576 / (((2 * delta : NNReal) : Real)) := by
    positivity
  have hratio :
      576 / (((2 * delta : NNReal) : Real)) <=
        5971968 / (delta : Real) := by
    have htwo : (((2 * delta : NNReal) : Real)) =
        2 * (delta : Real) := by norm_num
    rw [htwo]
    calc
      (576 : Real) / (2 * (delta : Real)) =
          288 / (delta : Real) := by ring
      _ <= 5971968 / (delta : Real) :=
        (div_le_div_iff_of_pos_right hdeltaReal).2 (by norm_num)
  unfold winnerSideBucketLoss selectedParentLogarithmicSideBucketLoss
  calc
    threeSideDyadicLoss (((2 * delta : NNReal) : Real)) 576 <=
        threeSideDyadicRatioLoss
          (576 / (((2 * delta : NNReal) : Real))) :=
      threeSideDyadicLoss_le_ratioLoss hlower (by norm_num)
    _ <= threeSideDyadicRatioLoss (5971968 / (delta : Real)) := by
      unfold threeSideDyadicRatioLoss
      apply Nat.pow_le_pow_left
      apply Int.toNat_le_toNat
      simpa only [add_comm] using
        (add_le_add_right (dyadicCeilBucket_mono hratioPos hratio) 1)

/-- Any source-scale power which absorbs the existing selected-parent
logarithmic loss also absorbs the outer winner-side loss. -/
theorem winnerSideBucketLoss_le_rpow
    {delta : NNReal} {lossEta : Real}
    (hdelta : 0 < delta) (hlossEta : 0 < lossEta)
    (hsmall : delta <=
      selectedParentLogarithmicSideBucketAbsorptionThreshold 1 lossEta) :
    (winnerSideBucketLoss delta : ENNReal) <=
      (delta : ENNReal) ^ (-lossEta) := by
  calc
    (winnerSideBucketLoss delta : ENNReal) <=
        (selectedParentLogarithmicSideBucketLoss delta : ENNReal) := by
      exact_mod_cast
        winnerSideBucketLoss_le_selectedParentLogarithmicSideBucketLoss
          delta hdelta
    _ <= (delta : ENNReal) ^ (-lossEta) :=
      selectedParentLogarithmicSideBucketLoss_le_rpow
        hlossEta hdelta hsmall

#print axioms
  winnerSideBucketLoss_le_selectedParentLogarithmicSideBucketLoss
#print axioms winnerSideBucketLoss_le_rpow

end Family8SelectedOccurrenceWinnerSideBucketLossPowerV1
