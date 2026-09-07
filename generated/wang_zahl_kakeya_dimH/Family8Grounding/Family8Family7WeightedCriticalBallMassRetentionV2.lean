import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7WeightedCriticalBallMassRetentionV2

open Family8Family7NativeHighWeightedCriticalBallV1
open FamilyStickyCinematicL32Lemma57CriticalScaleCarrierV1

noncomputable section

/-!
# Exact mass retention of the weighted critical ball

This is the ADD-only successor of V1.  It uses `gcongr` for the three
monotone ENNReal multiplications; the theorem statements and the exact
no-extra-scale-loss argument are unchanged.
-/

/-- Every source occurrence weight is bounded by the total weight inside the
one selected weighted critical ball. -/
theorem weight_le_criticalBallWeight
    {alpha : Type*} [DecidableEq alpha]
    (D : WeightedCanonicalNormBallData alpha)
    {i : alpha} (hi : i ∈ D.family) :
    D.weight i ≤ ∑ j ∈ D.criticalBall, D.weight j := by
  classical
  let q : ENNReal :=
    (ENNReal.ofReal D.delta) ^ (-D.exponent)
  have hdeltaENNPos : 0 < ENNReal.ofReal D.delta :=
    ENNReal.ofReal_pos.mpr D.delta_pos
  have hq0 : q ≠ 0 :=
    (ENNReal.rpow_pos hdeltaENNPos (by simp)).ne'
  have hqtop : q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hdeltaENNPos.ne' (by simp)
  have hiCandidate :
      i ∈ D.family.filter fun j => D.distance j i ≤ D.delta := by
    rw [Finset.mem_filter]
    exact ⟨hi, D.self_le_delta i hi⟩
  have hmass :
      D.weight i ≤
        finiteWeightedBallMass D.family D.distance D.weight D.delta i := by
    unfold finiteWeightedBallMass
    exact Finset.single_le_sum
      (fun _ _ => show (0 : ENNReal) ≤ _ from bot_le) hiCandidate
  have hdeltaCarrier :
      D.delta ∈ finiteCriticalScaleCarrier D.family D.distance
        D.delta D.ceiling := by
    simp [finiteCriticalScaleCarrier]
  have hdom := D.weighted_score_dominates_on_criticalCarrier
    hdeltaCarrier hi
  have hscale : D.delta ≤ D.criticalScale := D.criticalScale_bounds.1
  have hcriticalPos : 0 < D.criticalScale := D.delta_pos.trans_le hscale
  have hfactor :
      (ENNReal.ofReal D.criticalScale) ^ (-D.exponent) ≤ q := by
    have hreal :
        D.criticalScale ^ (-D.exponent) ≤ D.delta ^ (-D.exponent) :=
      Real.rpow_le_rpow_of_nonpos D.delta_pos hscale
        (neg_nonpos.mpr D.exponent_nonneg)
    have henn := ENNReal.ofReal_le_ofReal hreal
    simpa only [q, ENNReal.ofReal_rpow_of_pos hcriticalPos,
      ENNReal.ofReal_rpow_of_pos D.delta_pos] using henn
  rw [← ENNReal.mul_le_mul_iff_right hq0 hqtop]
  calc
    q * D.weight i = D.weight i * q := by ac_rfl
    _ ≤ finiteWeightedBallMass D.family D.distance D.weight D.delta i * q := by
      gcongr
    _ = finiteWeightedTwoEndsScore D.family D.distance D.weight
        D.exponent D.delta i := by rfl
    _ ≤ finiteWeightedTwoEndsScore D.family D.distance D.weight
        D.exponent D.criticalScale D.criticalCenter := hdom
    _ = (∑ j ∈ D.criticalBall, D.weight j) *
        (ENNReal.ofReal D.criticalScale) ^ (-D.exponent) := by
      rw [finiteWeightedTwoEndsScore,
        WeightedCanonicalNormBallData.finiteWeightedBallMass_criticalScale]
    _ ≤ (∑ j ∈ D.criticalBall, D.weight j) * q := by
      gcongr
    _ = q * (∑ j ∈ D.criticalBall, D.weight j) := by ac_rfl

/-- The total occurrence weight is retained by the selected weighted ball up
to exactly the number of source indices, with no scale-ratio loss. -/
theorem totalWeight_le_card_mul_criticalBallWeight
    {alpha : Type*} [DecidableEq alpha]
    (D : WeightedCanonicalNormBallData alpha) :
    (∑ i ∈ D.family, D.weight i) ≤
      (D.family.card : ENNReal) *
        (∑ i ∈ D.criticalBall, D.weight i) := by
  classical
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_max_image D.family D.weight D.family_nonempty
  have hsum := Finset.sum_le_card_nsmul D.family D.weight (D.weight i)
    (fun j hj => hmax j hj)
  calc
    (∑ j ∈ D.family, D.weight j) ≤
        (D.family.card : ENNReal) * D.weight i := by
      simpa only [nsmul_eq_mul] using hsum
    _ ≤ (D.family.card : ENNReal) *
        (∑ j ∈ D.criticalBall, D.weight j) := by
      gcongr
      exact weight_le_criticalBallWeight D hi

#print axioms weight_le_criticalBallWeight
#print axioms totalWeight_le_card_mul_criticalBallWeight

end

end Family8Family7WeightedCriticalBallMassRetentionV2
