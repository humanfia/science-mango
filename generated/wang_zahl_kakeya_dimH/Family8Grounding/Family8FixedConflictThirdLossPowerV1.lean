import Family8Grounding.Family8EighthSelectedThirdFactorPowerLossAbsorptionV3
import Family8Grounding.Family8FixedConflictLossPowerV3
import Mathlib.Tactic

/-!
# Power bound for the literal fixed-conflict third loss

This scalar module combines the exact fixed conflict-loss power with the
existing eighth-normalization absorption.  It has no dependent assembly or
long-core inputs.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FixedConflictThirdLossPowerV1

open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EighthSelectedThirdFactorPowerLossAbsorptionV3
open Family8FixedConflictLossPowerV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

def fixedConflictThirdLossSmallDeltaThreshold
    (conflictAbsorb thirdAbsorb epsilon gamma : Real) : NNReal :=
  min (fixedConflictLossSmallDeltaThreshold conflictAbsorb)
    (finiteConstantSmallDeltaThreshold
      (eighthSelectedThirdNormalizationLoss epsilon gamma) thirdAbsorb)

theorem fixedConflictThirdLossSmallDeltaThreshold_pos
    (conflictAbsorb thirdAbsorb epsilon gamma : Real) :
    0 < fixedConflictThirdLossSmallDeltaThreshold
      conflictAbsorb thirdAbsorb epsilon gamma := by
  exact lt_min
    (fixedConflictLossSmallDeltaThreshold_pos _)
    (finiteConstantSmallDeltaThreshold_pos _ _)

/-- The literal third loss has one Katz--Tao exponent, its radius exponent,
and two fixed-coefficient absorption exponents. -/
theorem fixedConflict_thirdLoss_le_delta_negativePower
    {delta rho : NNReal} {CKT : ENNReal}
    {etaKT conflictAbsorb thirdAbsorb epsilon gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hrho : 0 < rho) (hdeltaRho : delta <= rho)
    (hetaKT : 0 <= etaKT) (hepsilon : 0 <= epsilon)
    (hCKTfinite : CKT ≠ ∞)
    (hCKT : CKT <= (delta : ENNReal) ^ (-etaKT))
    (hconflictAbsorb : 0 < conflictAbsorb)
    (hthirdAbsorb : 0 < thirdAbsorb)
    (hsmall : delta <= fixedConflictThirdLossSmallDeltaThreshold
      conflictAbsorb thirdAbsorb epsilon gamma) :
    eighthSelectedThirdFactorLoss rho
        ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) epsilon gamma <=
      (delta : ENNReal) ^
        (-((etaKT + conflictAbsorb) + epsilon + thirdAbsorb)) := by
  have hloss :
      ((Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) <=
        (delta : ENNReal) ^ (-(etaKT + conflictAbsorb)) :=
    fixedConflictLoss_le_delta_negativePower
      hdelta hdeltaOne hetaKT hCKTfinite hCKT hconflictAbsorb
        (hsmall.trans (min_le_left _ _))
  exact eighthSelectedThirdFactorLoss_le_delta_negativePower_of_lossPower
    hdelta hrho hdeltaRho hepsilon hloss hthirdAbsorb
      (hsmall.trans (min_le_right _ _))

#print axioms fixedConflictThirdLossSmallDeltaThreshold_pos
#print axioms fixedConflict_thirdLoss_le_delta_negativePower

end
end Family8FixedConflictThirdLossPowerV1
