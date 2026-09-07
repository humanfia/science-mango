import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Proposition 6.6(A) as one collapsed Section-8 factor

This file only reassociates the exact Proposition 6.6(A) scalar.  The outer
and inner factors at the source scale equal one explicit coefficient times
the single Section-8 scale-count factor from `delta` to one.  Consequently a
same-object proof may keep the product count literal and isolate every
analytic loss in one coefficient comparison, without constructing a stronger
three-scale package or changing a selected block.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8Prop66ASectionEightCollapsedAlgebraV1

open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8ThreeScaleFrostmanFactorAlgebraV2

noncomputable section

/-- The exact coefficient left after identifying the Proposition 6.6(A)
card-scale factor with the Section-8 factor on `delta -> 1`. -/
def proposition66ASectionEightCoefficient
    (delta a b : NNReal) (CF : ENNReal)
    (epsilon beta : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon) *
    CF ^ (1 - beta / 2) *
      ((a : ENNReal) / (b : ENNReal)) ^ (3 * beta / 2)

/-- Lossless scalar identity; no multiplicity estimate is asserted. -/
theorem proposition66AFrostmanFactor_eq_coefficient_mul_sectionEight
    (delta a b : NNReal) (tubeCount : Nat)
    (CF : ENNReal) (epsilon beta : Real) :
    proposition66AFrostmanFactor delta a b tubeCount CF epsilon beta =
      proposition66ASectionEightCoefficient delta a b CF epsilon beta *
        sectionEightScaleCountFrostmanFactor delta 1 tubeCount beta := by
  unfold proposition66AFrostmanFactor
    proposition66ASectionEightCoefficient
    sectionEightScaleCountFrostmanFactor
    proposition66ACardScaleVolume
  simp only [ENNReal.coe_one, div_one]
  ac_rfl

/-- Exact outer-times-inner form with the literal product count. -/
theorem proposition66AOuter_mul_inner_eq_coefficient_mul_sectionEight
    {delta a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1) :
    proposition66AOuterFactor delta a b plankCount CF epsilon beta *
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta =
      proposition66ASectionEightCoefficient delta a b CF epsilon beta *
        sectionEightScaleCountFrostmanFactor delta 1
          (plankCount * tubesPerPlank) beta := by
  rw [proposition66AOuterFactor_mul_innerFactor_eq_frostmanFactor
    hdelta ha hb hbeta hbetaOne rfl]
  exact proposition66AFrostmanFactor_eq_coefficient_mul_sectionEight
    delta a b (plankCount * tubesPerPlank) CF epsilon beta

/-- Consumer-weak inequality: all analytic losses are paid only through the
displayed coefficient, while the product count remains unchanged. -/
theorem proposition66AOuter_mul_inner_le_loss_mul_sectionEight
    {delta a b : NNReal} {plankCount tubesPerPlank : Nat}
    {CF loss : ENNReal} {epsilon beta : Real}
    (hdelta : 0 < delta) (ha : 0 < a) (hb : 0 < b)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1)
    (hcoefficient :
      proposition66ASectionEightCoefficient delta a b CF epsilon beta <=
        loss) :
    proposition66AOuterFactor delta a b plankCount CF epsilon beta *
        proposition66AInnerFactor delta a b tubesPerPlank epsilon beta <=
      loss * sectionEightScaleCountFrostmanFactor delta 1
        (plankCount * tubesPerPlank) beta := by
  rw [proposition66AOuter_mul_inner_eq_coefficient_mul_sectionEight
    hdelta ha hb hbeta hbetaOne]
  exact mul_le_mul' hcoefficient le_rfl

#print axioms proposition66ASectionEightCoefficient
#print axioms proposition66AFrostmanFactor_eq_coefficient_mul_sectionEight
#print axioms proposition66AOuter_mul_inner_eq_coefficient_mul_sectionEight
#print axioms proposition66AOuter_mul_inner_le_loss_mul_sectionEight

end
end Family8Prop66ASectionEightCollapsedAlgebraV1
