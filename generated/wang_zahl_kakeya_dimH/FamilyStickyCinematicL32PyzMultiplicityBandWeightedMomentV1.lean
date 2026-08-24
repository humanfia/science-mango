import FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

set_option autoImplicit false

open Set
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzMultiplicityBandWeightedMomentV1

open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1

noncomputable section

/-!
# Multiplicity-band lower endpoint for a weighted three-halves moment

This is the denominator-free numerical transport used at the first PYZ
multiplicity refinement.  Membership in the literal finite multiplicity band
produces the lower cardinality bound; the desired moment estimate is not a
field of the source data.
-/

theorem multiplicityBand_lower_weighted_rpow_mul_le
    {point index : Type*} [MeasurableSpace point]
    (Z : FiniteProjectedShading point index)
    {lower upper : Nat} {x : point}
    (hx : x ∈ Z.multiplicityBand lower upper)
    {weightOne weightTwo : Real} (hweightOne : 0 ≤ weightOne)
    (hweightTwo : 0 ≤ weightTwo) {mass bound : ENNReal}
    (hactive :
      (ENNReal.ofReal (((Z.activeAtPoint x).card : Real) * weightOne *
        weightTwo)) ^ (3 / 2 : Real) * mass ≤ bound) :
    (ENNReal.ofReal ((lower : Real) * weightOne * weightTwo)) ^
        (3 / 2 : Real) * mass ≤ bound := by
  have hlowerNat : lower ≤ (Z.activeAtPoint x).card :=
    (Z.mem_multiplicityBand.mp hx).2.1
  have hlowerReal : (lower : Real) ≤ (Z.activeAtPoint x).card := by
    exact_mod_cast hlowerNat
  have hweighted : (lower : Real) * weightOne * weightTwo ≤
      ((Z.activeAtPoint x).card : Real) * weightOne * weightTwo := by
    gcongr
  calc
    (ENNReal.ofReal ((lower : Real) * weightOne * weightTwo)) ^
          (3 / 2 : Real) * mass ≤
        (ENNReal.ofReal (((Z.activeAtPoint x).card : Real) * weightOne *
          weightTwo)) ^ (3 / 2 : Real) * mass := by
      gcongr
    _ ≤ bound := hactive

#print axioms multiplicityBand_lower_weighted_rpow_mul_le

end

end FamilyStickyCinematicL32PyzMultiplicityBandWeightedMomentV1
