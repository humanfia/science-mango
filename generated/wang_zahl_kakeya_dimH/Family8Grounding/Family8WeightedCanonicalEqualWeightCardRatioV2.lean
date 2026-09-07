import Family8Grounding.Family8WeightedCanonicalBallMassRatioV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

open scoped BigOperators ENNReal

namespace Family8WeightedCanonicalEqualWeightCardRatioV2

open Family8Family7NativeHighWeightedCriticalBallV1
open Family8WeightedCanonicalBallMassRatioV1

noncomputable section

universe u

/-- On a nonzero finite exact-weight family, weighted critical-scale
nonconcentration cancels to the literal cardinal ratio estimate. -/
theorem ballCard_le_ratio_rpow_mul_criticalBallCard
    {alpha : Type u} (D : WeightedCanonicalNormBallData alpha)
    (value : ENNReal)
    (hcommon : ∀ i, i ∈ D.family → D.weight i = value)
    (hvalue0 : value ≠ 0) (hvalueTop : value ≠ ∞)
    {radius : Real} (hradiusLower : D.delta ≤ radius)
    (hradiusUpper : radius ≤ D.ceiling)
    (testCenter : alpha) (htestCenter : testCenter ∈ D.family) :
    ((D.family.filter fun i => D.distance i testCenter ≤ radius).card :
        ENNReal) ≤
      ((ENNReal.ofReal radius) / ENNReal.ofReal D.criticalScale) ^
          D.exponent *
        (D.criticalBall.card : ENNReal) := by
  have htestMass :
      finiteWeightedBallMass D.family D.distance D.weight radius testCenter =
        ((D.family.filter fun i => D.distance i testCenter ≤ radius).card :
          ENNReal) * value := by
    unfold finiteWeightedBallMass
    calc
      (∑ i ∈ D.family.filter fun j => D.distance j testCenter ≤ radius,
          D.weight i) =
          ∑ _i ∈ D.family.filter
              (fun j => D.distance j testCenter ≤ radius), value := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcommon i (Finset.filter_subset _ _ hi)
      _ = ((D.family.filter fun j =>
          D.distance j testCenter ≤ radius).card : ENNReal) * value := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hcriticalMass :
      (∑ i ∈ D.criticalBall, D.weight i) =
        (D.criticalBall.card : ENNReal) * value := by
    calc
      (∑ i ∈ D.criticalBall, D.weight i) =
          ∑ _i ∈ D.criticalBall, value := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcommon i (D.criticalBall_subset_family hi)
      _ = (D.criticalBall.card : ENNReal) * value := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hweighted := weightedBallMass_le_ratio_rpow_mul_criticalBallMass
    D hradiusLower hradiusUpper testCenter htestCenter
  have hscaled :
      ((D.family.filter fun i => D.distance i testCenter ≤ radius).card :
          ENNReal) * value ≤
        (((ENNReal.ofReal radius) / ENNReal.ofReal D.criticalScale) ^
            D.exponent * (D.criticalBall.card : ENNReal)) * value := by
    calc
      ((D.family.filter fun i => D.distance i testCenter ≤ radius).card :
          ENNReal) * value =
          finiteWeightedBallMass D.family D.distance D.weight radius
            testCenter := htestMass.symm
      _ ≤ ((ENNReal.ofReal radius) / ENNReal.ofReal D.criticalScale) ^
            D.exponent * ∑ i ∈ D.criticalBall, D.weight i := hweighted
      _ = (((ENNReal.ofReal radius) / ENNReal.ofReal D.criticalScale) ^
            D.exponent * (D.criticalBall.card : ENNReal)) * value := by
        rw [hcriticalMass]
        ac_rfl
  exact (ENNReal.mul_le_mul_iff_left hvalue0 hvalueTop).mp hscaled

end

end Family8WeightedCanonicalEqualWeightCardRatioV2
