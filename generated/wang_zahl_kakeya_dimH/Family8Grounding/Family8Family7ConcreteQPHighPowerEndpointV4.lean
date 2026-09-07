import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPAggregationV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8Family7ConcreteQPHighPowerEndpointV4

open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPAggregationV3

noncomputable section

/-!
# Power endpoint after concrete-Q/P cross-center aggregation

V3 referred to an obsolete right-multiplication lemma name.  This successor
uses the current `mul_le_mul_right` and normalizes the commutative products.
-/

/-- A finite positive base converts a coefficient upper power into the
corresponding extra exponent in the mass lower bound. -/
theorem rpow_add_le_of_source_le_coefficient_mul
    {d source coefficient mass : ENNReal}
    {sourceExp costExp : Real}
    (hd0 : d ≠ 0) (hdTop : d ≠ ∞)
    (hfloor : d ^ sourceExp <= source)
    (hsource : source <= coefficient * mass)
    (hcoefficient : coefficient <= d ^ (-costExp)) :
    d ^ (sourceExp + costExp) <= mass := by
  have hsourceMul :
      d ^ sourceExp * d ^ costExp <=
        (coefficient * mass) * d ^ costExp := by
    simpa only [mul_comm] using
      (mul_le_mul_right (hfloor.trans hsource) (d ^ costExp))
  have hcoefficientMul :
      coefficient * mass <= d ^ (-costExp) * mass := by
    simpa only [mul_comm] using
      (mul_le_mul_right hcoefficient mass)
  calc
    d ^ (sourceExp + costExp) =
        d ^ sourceExp * d ^ costExp := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ <= (coefficient * mass) * d ^ costExp := hsourceMul
    _ <= (d ^ (-costExp) * mass) * d ^ costExp := by
      simpa only [mul_comm] using
        (mul_le_mul_right hcoefficientMul (d ^ costExp))
    _ = (d ^ (-costExp) * d ^ costExp) * mass := by
      ac_rfl
    _ = mass := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
      norm_num

/-- Specialized endpoint for the actual common physical mass exposed by the
concrete-Q/P cross-center consumer. -/
theorem nativeHighPhysicalMass_power_lower
    {radius : NNReal} {iota : Type*} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota}
    {delta : NNReal} {totalCoefficient : ENNReal}
    {sourceExp costExp : Real}
    (hdelta : 0 < delta)
    (hsourceFloor : (delta : ENNReal) ^ sourceExp <= D.sourceMass / 2)
    (haggregate : D.sourceMass / 2 <=
      totalCoefficient * nativeHighPhysicalMass D)
    (hcoefficient : totalCoefficient <=
      (delta : ENNReal) ^ (-costExp)) :
    (delta : ENNReal) ^ (sourceExp + costExp) <=
      nativeHighPhysicalMass D := by
  exact rpow_add_le_of_source_le_coefficient_mul
    (ENNReal.coe_ne_zero.mpr hdelta.ne') ENNReal.coe_ne_top
      hsourceFloor haggregate hcoefficient

#print axioms rpow_add_le_of_source_le_coefficient_mul
#print axioms nativeHighPhysicalMass_power_lower

end
end Family8Family7ConcreteQPHighPowerEndpointV4
