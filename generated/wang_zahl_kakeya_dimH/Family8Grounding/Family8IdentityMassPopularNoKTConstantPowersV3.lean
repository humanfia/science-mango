import Family8Grounding.Family8IdentityMassPopularNoKTPowerEnvelopeV3
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Small-delta absorption of the identity no-KT mass-popular constants
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8IdentityMassPopularNoKTConstantPowersV3

open Family8IdentityMassPopularNoKTPowerEnvelopeV3
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable def identityMassPopularDensityPowerThreshold (absorbExp : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    identityMassPopularDensityFixedConstant absorbExp

noncomputable def identityMassPopularBasePowerThreshold
    (eta p a absorbExp : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (identityMassPopularBaseFixedConstant eta p a) absorbExp

theorem identityMassPopularDensityFixedConstant_ne_top :
    identityMassPopularDensityFixedConstant ≠ ∞ := by
  norm_num [identityMassPopularDensityFixedConstant]

theorem identityMassPopularBaseFixedConstant_ne_top (eta p a : Real) :
    identityMassPopularBaseFixedConstant eta p a ≠ ∞ := by
  unfold identityMassPopularBaseFixedConstant
  apply ENNReal.mul_ne_top
  · norm_num
  · apply ENNReal.rpow_ne_top_of_ne_zero
    · norm_num
    · exact ENNReal.div_ne_top (by norm_num) (by norm_num)

theorem identityMassPopularDensityFixedConstant_le_power
    {delta : NNReal} {absorbExp : Real}
    (habsorbExp : 0 < absorbExp) (hdelta : 0 < delta)
    (hsmall : delta ≤ identityMassPopularDensityPowerThreshold absorbExp) :
    identityMassPopularDensityFixedConstant ≤
      (delta : ENNReal) ^ (-absorbExp) :=
  finiteConstant_le_delta_negativePower
    identityMassPopularDensityFixedConstant_ne_top
      habsorbExp hdelta hsmall

theorem identityMassPopularBaseFixedConstant_le_power
    {delta : NNReal} {eta p a absorbExp : Real}
    (habsorbExp : 0 < absorbExp) (hdelta : 0 < delta)
    (hsmall : delta ≤
      identityMassPopularBasePowerThreshold eta p a absorbExp) :
    identityMassPopularBaseFixedConstant eta p a ≤
      (delta : ENNReal) ^ (-absorbExp) :=
  finiteConstant_le_delta_negativePower
    (identityMassPopularBaseFixedConstant_ne_top eta p a)
      habsorbExp hdelta hsmall

#print axioms identityMassPopularDensityFixedConstant_ne_top
#print axioms identityMassPopularBaseFixedConstant_ne_top
#print axioms identityMassPopularDensityFixedConstant_le_power
#print axioms identityMassPopularBaseFixedConstant_le_power

end Family8IdentityMassPopularNoKTConstantPowersV3
