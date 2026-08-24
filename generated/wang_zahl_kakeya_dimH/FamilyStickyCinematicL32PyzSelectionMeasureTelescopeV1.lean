import Mathlib.Data.ENNReal.Inv

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32PyzSelectionMeasureTelescopeV1

/-!
# Denominator-free telescope for the five PYZ selections

The low branch uses, in order, an initial multiplicity band, a norm-scale
cell, one norm-cover centre, a tangency-scale cell, and a final positive
multiplicity cell.  Each selector returns a lower bound after division by a
finite positive loss.  This module converts those five bounds into one
cross-multiplied estimate; it contains no geometric or probabilistic input.
-/

theorem div_retention_to_mul_upper
    {source retained loss : ENNReal}
    (hlossZero : loss ≠ 0) (hlossTop : loss ≠ ⊤)
    (hretained : source / loss ≤ retained) :
    source ≤ retained * loss :=
  (ENNReal.div_le_iff hlossZero hlossTop).mp hretained

theorem five_stage_div_retention_telescope
    {source stageOne stageTwo stageThree stageFour retained : ENNReal}
    {lossOne lossTwo lossThree lossFour lossFive : ENNReal}
    (hlossOneZero : lossOne ≠ 0) (hlossOneTop : lossOne ≠ ⊤)
    (hlossTwoZero : lossTwo ≠ 0) (hlossTwoTop : lossTwo ≠ ⊤)
    (hlossThreeZero : lossThree ≠ 0) (hlossThreeTop : lossThree ≠ ⊤)
    (hlossFourZero : lossFour ≠ 0) (hlossFourTop : lossFour ≠ ⊤)
    (hlossFiveZero : lossFive ≠ 0) (hlossFiveTop : lossFive ≠ ⊤)
    (hOne : source / lossOne ≤ stageOne)
    (hTwo : stageOne / lossTwo ≤ stageTwo)
    (hThree : stageTwo / lossThree ≤ stageThree)
    (hFour : stageThree / lossFour ≤ stageFour)
    (hFive : stageFour / lossFive ≤ retained) :
    source ≤
      (lossOne * lossTwo * lossThree * lossFour * lossFive) * retained := by
  have hOne' := div_retention_to_mul_upper hlossOneZero hlossOneTop hOne
  have hTwo' := div_retention_to_mul_upper hlossTwoZero hlossTwoTop hTwo
  have hThree' := div_retention_to_mul_upper
    hlossThreeZero hlossThreeTop hThree
  have hFour' := div_retention_to_mul_upper hlossFourZero hlossFourTop hFour
  have hFive' := div_retention_to_mul_upper hlossFiveZero hlossFiveTop hFive
  calc
    source ≤ stageOne * lossOne := hOne'
    _ ≤ (stageTwo * lossTwo) * lossOne := mul_le_mul_left hTwo' lossOne
    _ ≤ ((stageThree * lossThree) * lossTwo) * lossOne := by
      exact mul_le_mul_left (mul_le_mul_left hThree' lossTwo) lossOne
    _ ≤ (((stageFour * lossFour) * lossThree) * lossTwo) * lossOne := by
      exact mul_le_mul_left
        (mul_le_mul_left (mul_le_mul_left hFour' lossThree) lossTwo) lossOne
    _ ≤ ((((retained * lossFive) * lossFour) * lossThree) * lossTwo) *
        lossOne := by
      exact mul_le_mul_left
        (mul_le_mul_left
          (mul_le_mul_left (mul_le_mul_left hFive' lossFour) lossThree)
          lossTwo) lossOne
    _ = (lossOne * lossTwo * lossThree * lossFour * lossFive) * retained := by
      ac_rfl

#print axioms div_retention_to_mul_upper
#print axioms five_stage_div_retention_telescope

end FamilyStickyCinematicL32PyzSelectionMeasureTelescopeV1
