import Family8Grounding.Family8OuterCountAggregatePowerBudgetV2
import Mathlib.Tactic

/-!
# Identity-first outer/count aggregate power

At the endpoint long core the first loss is exactly one.  This projection is
the scalar specialization of the general outer/count budget used by the
literal three-scale DSO record.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreIdentityFirstAggregatePowerV1

open Family8OuterCountAggregatePowerBudgetV2

noncomputable section

/-- A third-loss power and a count-loss power give the exact aggregate-loss
field when the first loss is the endpoint identity value one. -/
theorem identityFirst_thirdCountAggregateLoss_le_threeEta
    {delta : NNReal} {thirdLoss countLoss : ENNReal}
    {thirdExponent countExponent eta gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hgammaTwo : gamma <= 2)
    (hThird : thirdLoss <= (delta : ENNReal) ^ (-thirdExponent))
    (hCount : countLoss <= (delta : ENNReal) ^ (-countExponent))
    (hExponent : thirdExponent +
      countExponent * (1 - gamma / 2) <= 3 * eta) :
    ((1 * thirdLoss) * countLoss ^ (1 - gamma / 2)) <=
      (delta : ENNReal) ^ (-3 * eta) := by
  exact outerCountAggregateLoss_le_threeEta
    hdelta hdeltaOne hgammaTwo
      (firstLoss := (1 : ENNReal)) (thirdLoss := thirdLoss)
      (countLoss := countLoss) (firstExponent := 0)
      (thirdExponent := thirdExponent) (countExponent := countExponent)
      (eta := eta) (gamma := gamma) (by norm_num) hThird hCount (by
        simpa only [zero_add] using hExponent)

#print axioms identityFirst_thirdCountAggregateLoss_le_threeEta

end
end Family8EndpointLongCoreIdentityFirstAggregatePowerV1
