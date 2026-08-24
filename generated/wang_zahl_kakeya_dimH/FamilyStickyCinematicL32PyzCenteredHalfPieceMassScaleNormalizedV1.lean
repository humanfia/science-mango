import FamilyStickyCinematicL32PyzCenteredHalfPieceMassUpperCleanV1
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzCenteredHalfPieceMassScaleNormalizedV1

open FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1
open FamilyStickyCinematicL32PyzCenteredHalfPieceMassUpperCleanV1

noncomputable section

/-!
# Scale normalization of the centered-half piece mass

For the paper range `0 ≤ alpha ≤ 1`, the two Frostman thickness factors
combine exactly into the physical scale power `radius^(2-alpha)`.  The only
loss retained here is the explicit factor `2^alpha` coming from the width
`2 * radius` of the graph strip.
-/

theorem dropped_centeredHalf_pieceMass_eq_scale_power
    (radius : NNReal) (alpha : Real) (C : ENNReal)
    (halpha : 0 ≤ alpha) (halphaOne : alpha ≤ 1) :
    (C * (ENNReal.ofReal (radius : Real)) ^ (1 - alpha) *
          (ENNReal.ofReal (2 * (radius : Real))) ^ alpha) *
        (C * (ENNReal.ofReal (radius : Real)) ^ (1 - alpha)) =
      (C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha *
        (ENNReal.ofReal (radius : Real)) ^ (2 - alpha) := by
  let r : ENNReal := ENNReal.ofReal (radius : Real)
  have honeSub : 0 ≤ 1 - alpha := sub_nonneg.mpr halphaOne
  have htwo : ENNReal.ofReal (2 * (radius : Real)) =
      ENNReal.ofReal (2 : Real) * r := by
    simpa only [r] using ENNReal.ofReal_mul
      (show (0 : Real) ≤ 2 by norm_num)
  rw [htwo, ENNReal.mul_rpow_of_nonneg _ _ halpha]
  calc
    (C * r ^ (1 - alpha) *
          ((ENNReal.ofReal (2 : Real)) ^ alpha * r ^ alpha)) *
        (C * r ^ (1 - alpha)) =
      ((C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha) *
        ((r ^ (1 - alpha) * r ^ alpha) * r ^ (1 - alpha)) := by
          ring
    _ = ((C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha) *
        (r ^ ((1 - alpha) + alpha) * r ^ (1 - alpha)) := by
          rw [ENNReal.rpow_add_of_nonneg (1 - alpha) alpha honeSub halpha]
    _ = ((C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha) *
        (r ^ (1 + (1 - alpha))) := by
          rw [ENNReal.rpow_add_of_nonneg 1 (1 - alpha) (by norm_num) honeSub]
          ring
    _ = (C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha *
        r ^ (2 - alpha) := by
          rw [show 1 + (1 - alpha) = 2 - alpha by ring]

theorem pyzActualCenteredHalfY1FrostmanPieceMass_le_scale_power
    {radius : NNReal} {alpha : Real} {C : ENNReal} {A B : Real}
    (halpha : 0 ≤ alpha) (halphaOne : alpha ≤ 1)
    (hAB : A ≤ B) (hparameter : ∀ z ∈ Set.Icc A B, |z| ≤ 1) :
    pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B ≤
      (C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha *
        (ENNReal.ofReal (radius : Real)) ^ (2 - alpha) := by
  exact (pyzActualCenteredHalfY1FrostmanPieceMass_le_drop_interval
    halpha hAB hparameter).trans_eq
      (dropped_centeredHalf_pieceMass_eq_scale_power radius alpha C
        halpha halphaOne)

#print axioms dropped_centeredHalf_pieceMass_eq_scale_power
#print axioms pyzActualCenteredHalfY1FrostmanPieceMass_le_scale_power

end

end FamilyStickyCinematicL32PyzCenteredHalfPieceMassScaleNormalizedV1
