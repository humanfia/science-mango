import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8FrostmanRHSScaleVolumeAlgebraV3

open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-!
# Exact scale and volume algebra for the Frostman multiplicity RHS

These statements are purely algebraic.  They expose the constant-scale loss
and the exponent-improvement budget separately, without assuming the final
multiplicity estimate or a one-step self-improvement theorem.
-/

/-- Real powers commute with dividing a finite `NNReal` scale by eight. -/
theorem coe_div_eight_rpow
    (delta : NNReal) (a : Real) :
    (((delta / 8 : NNReal) : ENNReal) ^ a) =
      (delta : ENNReal) ^ a * (8 : ENNReal) ^ (-a) := by
  rw [ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0)]
  rw [div_eq_mul_inv,
    ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top (by finiteness) a,
    ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  norm_num

/-- Exact fixed-ratio conversion from radius `delta/8` back to radius
`delta`; the only price is `8^(epsilon+2 gamma)`. -/
theorem frostmanMultiplicityRHS_div_eight
    (delta : NNReal) (actualVolume : ENNReal)
    (epsilon gamma : Real) :
    frostmanMultiplicityRHS (delta / 8) actualVolume epsilon gamma =
      ((8 : ENNReal) ^ epsilon * (8 : ENNReal) ^ (2 * gamma)) *
        frostmanMultiplicityRHS delta actualVolume epsilon gamma := by
  unfold frostmanMultiplicityRHS
  rw [coe_div_eight_rpow delta (-epsilon),
    coe_div_eight_rpow delta (-2 * gamma)]
  ring_nf

#print axioms coe_div_eight_rpow
#print axioms frostmanMultiplicityRHS_div_eight

end
end Family8FrostmanRHSScaleVolumeAlgebraV3
