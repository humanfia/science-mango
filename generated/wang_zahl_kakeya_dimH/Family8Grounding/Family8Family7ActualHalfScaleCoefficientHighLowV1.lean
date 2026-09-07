import FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace Family8Family7ActualHalfScaleCoefficientHighLowV1

open FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1

/-! # Honest low/high split at the coefficient-cover threshold -/

theorem exactCard_low_or_exists_nativeMultiplicity
    (parallelLoss n : Nat) (hparallelLoss : 0 < parallelLoss) :
    n < 3 * (actualHalfScaleCoefficientCoverLoss * parallelLoss) ∨
      ∃ multiplicity : Nat,
        0 < multiplicity ∧
        3 * multiplicity ≤ n ∧
        actualHalfScaleCoefficientCoverLoss * parallelLoss ≤ multiplicity := by
  by_cases hhigh :
      3 * (actualHalfScaleCoefficientCoverLoss * parallelLoss) ≤ n
  · right
    refine ⟨actualHalfScaleCoefficientCoverLoss * parallelLoss,
      Nat.mul_pos ?_ hparallelLoss, hhigh, le_rfl⟩
    norm_num [actualHalfScaleCoefficientCoverLoss]
  · left
    omega

#print axioms exactCard_low_or_exists_nativeMultiplicity

end Family8Family7ActualHalfScaleCoefficientHighLowV1
