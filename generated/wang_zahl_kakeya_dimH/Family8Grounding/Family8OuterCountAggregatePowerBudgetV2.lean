import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8OuterCountAggregatePowerBudgetV2

noncomputable section

/-!
# Power algebra for the aggregate outer/count loss

Two analytic outer losses and the honest uniform-count loss are combined
below.  V1 was a failed associativity draft and is intentionally not
imported.
-/

theorem outerCountAggregateLoss_le_negativePower
    {delta : NNReal} {firstLoss thirdLoss countLoss : ENNReal}
    {firstExponent thirdExponent countExponent targetExponent gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hgammaTwo : gamma ≤ 2)
    (hFirst : firstLoss ≤ (delta : ENNReal) ^ (-firstExponent))
    (hThird : thirdLoss ≤ (delta : ENNReal) ^ (-thirdExponent))
    (hCount : countLoss ≤ (delta : ENNReal) ^ (-countExponent))
    (hexponent : firstExponent + thirdExponent +
      countExponent * (1 - gamma / 2) ≤ targetExponent) :
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
      (delta : ENNReal) ^ (-targetExponent) := by
  let q : Real := 1 - gamma / 2
  have hq : 0 ≤ q := by
    dsimp only [q]
    linarith
  have hexponent' : firstExponent + thirdExponent +
      countExponent * q ≤ targetExponent := by
    simpa only [q] using hexponent
  have hcountPow : countLoss ^ q ≤
      ((delta : ENNReal) ^ (-countExponent)) ^ q :=
    ENNReal.rpow_le_rpow hCount hq
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOneENN : (delta : ENNReal) ≤ 1 := by
    exact_mod_cast hdeltaOne
  calc
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
        (((delta : ENNReal) ^ (-firstExponent)) *
          ((delta : ENNReal) ^ (-thirdExponent))) *
            (((delta : ENNReal) ^ (-countExponent)) ^ q) := by
      simpa only [q] using
        (mul_le_mul' (mul_le_mul' hFirst hThird) hcountPow)
    _ = (((delta : ENNReal) ^ (-firstExponent)) *
          ((delta : ENNReal) ^ (-thirdExponent))) *
            (delta : ENNReal) ^ ((-countExponent) * q) := by
      rw [ENNReal.rpow_mul]
    _ = (delta : ENNReal) ^
          (((-firstExponent) + (-thirdExponent)) +
            ((-countExponent) * q)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop,
        ← ENNReal.rpow_add _ _ hd0 hdTop]
    _ = (delta : ENNReal) ^
          (-(firstExponent + thirdExponent + countExponent * q)) := by
      congr 1
      ring
    _ ≤ (delta : ENNReal) ^ (-targetExponent) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN
      linarith

theorem outerCountAggregateLoss_le_threeEta
    {delta : NNReal} {firstLoss thirdLoss countLoss : ENNReal}
    {firstExponent thirdExponent countExponent eta gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hgammaTwo : gamma ≤ 2)
    (hFirst : firstLoss ≤ (delta : ENNReal) ^ (-firstExponent))
    (hThird : thirdLoss ≤ (delta : ENNReal) ^ (-thirdExponent))
    (hCount : countLoss ≤ (delta : ENNReal) ^ (-countExponent))
    (hexponent : firstExponent + thirdExponent +
      countExponent * (1 - gamma / 2) ≤ 3 * eta) :
    (firstLoss * thirdLoss) * countLoss ^ (1 - gamma / 2) ≤
      (delta : ENNReal) ^ (-3 * eta) := by
  simpa only [neg_mul] using
    (outerCountAggregateLoss_le_negativePower
      hdelta hdeltaOne hgammaTwo hFirst hThird hCount hexponent)

#print axioms outerCountAggregateLoss_le_negativePower
#print axioms outerCountAggregateLoss_le_threeEta

end
end Family8OuterCountAggregatePowerBudgetV2
