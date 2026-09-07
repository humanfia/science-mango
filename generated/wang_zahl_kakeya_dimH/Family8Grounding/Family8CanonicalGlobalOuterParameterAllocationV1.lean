import Family8Grounding.Family8CanonicalBufferedGlobalLongIntervalOuterEndpointV1
import Family8Grounding.Family8Section8FixedPositiveSelfImprovementBudgetV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalGlobalOuterParameterAllocationV1

open Family8ParameterLadderV1
open Family8LongIntervalBootstrapNumericsV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8CanonicalBufferedGlobalLongIntervalOuterEndpointV1

noncomputable section

/-!
# Uniform numerical allocation for the canonical generalized outer estimate

All auxiliary polynomial-John, fresh-selection, cardinal and scale losses
are assigned one quantum.  The quantum is chosen from the source property
exponent and the ladder epsilon before the datum and stopping stage are
known.  Six copies fit inside the source density budget, while the complete
outer normalization uses far less than the universal `4 * epsilon` part of
the long-interval loss.
-/

def canonicalGlobalOuterQuantum
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (propertyEta : Real) : Real :=
  min propertyEta P.epsilon / 100

theorem canonicalGlobalOuterQuantum_pos
    {epsilon0 beta gamma propertyEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hpropertyEta : 0 < propertyEta) :
    0 < canonicalGlobalOuterQuantum P propertyEta := by
  unfold canonicalGlobalOuterQuantum
  exact div_pos (lt_min hpropertyEta P.epsilon_pos) (by norm_num)

theorem canonicalGlobalOuterQuantum_le_property_div
    {epsilon0 beta gamma propertyEta : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    canonicalGlobalOuterQuantum P propertyEta <= propertyEta / 100 := by
  unfold canonicalGlobalOuterQuantum
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem canonicalGlobalOuterQuantum_le_epsilon_div
    {epsilon0 beta gamma propertyEta : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    canonicalGlobalOuterQuantum P propertyEta <= P.epsilon / 100 := by
  unfold canonicalGlobalOuterQuantum
  exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

theorem canonicalGlobalOuter_density_budget
    {epsilon0 beta gamma propertyEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hpropertyEta : 0 < propertyEta) :
    let q := canonicalGlobalOuterQuantum P propertyEta
    2 * (q + q) + q + q <= propertyEta := by
  dsimp only
  have hq := canonicalGlobalOuterQuantum_le_property_div
    (P := P) (propertyEta := propertyEta)
  linarith

theorem canonicalGlobalOuter_coefficient_budget
    {epsilon0 beta gamma propertyEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hpropertyEta : 0 < propertyEta) :
    let q := canonicalGlobalOuterQuantum P propertyEta
    q + q + q <= propertyEta := by
  dsimp only
  have hq := canonicalGlobalOuterQuantum_le_property_div
    (P := P) (propertyEta := propertyEta)
  linarith

theorem canonicalGlobalOuter_generalizedLoss_nonneg
    {epsilon0 beta gamma propertyEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 <= beta) (hpropertyEta : 0 < propertyEta) :
    let q := canonicalGlobalOuterQuantum P propertyEta
    0 <= canonicalFullCoarseGeneralizedLoss
      (sectionEightFixedNu P) beta q q q q q := by
  dsimp only
  unfold canonicalFullCoarseGeneralizedLoss sectionEightFixedNu
  have hq : 0 <= canonicalGlobalOuterQuantum P propertyEta :=
    (canonicalGlobalOuterQuantum_pos P hpropertyEta).le
  have hbetaq : 0 <= beta *
      canonicalGlobalOuterQuantum P propertyEta := mul_nonneg hbeta hq
  have hnu := (P.eta_pos 0).le
  linarith

theorem canonicalGlobalOuter_longInterval_loss_budget
    {epsilon0 beta gamma propertyEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hbetaOne : beta <= 1)
    (hpropertyEta : 0 < propertyEta) (j : Nat) :
    let q := canonicalGlobalOuterQuantum P propertyEta
    canonicalFullCoarseGeneralizedLoss
          (sectionEightFixedNu P) beta q q q q q +
        q + q * (1 - beta) <=
      longIntervalDeltaLoss P.epsilon
        (10 * P.eta j / (P.epsilon * beta)) := by
  dsimp only
  let q := canonicalGlobalOuterQuantum P propertyEta
  have hqpos : 0 < q := canonicalGlobalOuterQuantum_pos P hpropertyEta
  have hqeps : q <= P.epsilon / 100 :=
    canonicalGlobalOuterQuantum_le_epsilon_div P
  have hbetaq : beta * q <= q := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hbetaOne hqpos.le)
  have honeSub : 0 <= 1 - beta := by linarith
  have hqOneSub : q * (1 - beta) <= q := by
    have honeSubOne : 1 - beta <= 1 := by linarith
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left honeSubOne hqpos.le)
  have hnu : sectionEightFixedNu P <= P.epsilon / 5 := by
    exact P.eta_le_epsilon_div_five 0
  have hetaPrime : 0 <=
      10 * P.eta j / (P.epsilon * beta) := by
    exact (div_pos (mul_pos (by norm_num) (P.eta_pos j))
      (mul_pos P.epsilon_pos hbeta)).le
  unfold canonicalFullCoarseGeneralizedLoss longIntervalDeltaLoss
  linarith

#print axioms canonicalGlobalOuterQuantum_pos
#print axioms canonicalGlobalOuterQuantum_le_property_div
#print axioms canonicalGlobalOuterQuantum_le_epsilon_div
#print axioms canonicalGlobalOuter_density_budget
#print axioms canonicalGlobalOuter_coefficient_budget
#print axioms canonicalGlobalOuter_generalizedLoss_nonneg
#print axioms canonicalGlobalOuter_longInterval_loss_budget

end
end Family8CanonicalGlobalOuterParameterAllocationV1
