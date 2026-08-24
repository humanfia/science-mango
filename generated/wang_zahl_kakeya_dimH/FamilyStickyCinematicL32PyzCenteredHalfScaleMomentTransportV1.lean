import FamilyStickyCinematicL32PyzCenteredHalfPieceMassScaleNormalizedV1

set_option autoImplicit false

open Set
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzCenteredHalfScaleMomentTransportV1

open FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1
open FamilyStickyCinematicL32PyzCenteredHalfPieceMassScaleNormalizedV1

noncomputable section

/-!
# Monotone transport of the low moment to the physical scale power

This is a reusable algebraic connector.  Its premise is an already-proved
moment inequality, not a source-geometric hypothesis; actual endpoint
wrappers invoke it immediately on the faithful WZ-L3 moment theorem.
-/

theorem moment_pieceMass_le_scalePower
    {lhs prefactor count : ENNReal}
    {radius : NNReal} {alpha : Real} {C : ENNReal} {A B : Real}
    (halpha : 0 ≤ alpha) (halphaOne : alpha ≤ 1)
    (hAB : A ≤ B) (hparameter : ∀ z ∈ Set.Icc A B, |z| ≤ 1)
    (hmoment : lhs ≤ prefactor *
      (count * pyzActualCenteredHalfY1FrostmanPieceMass
        radius alpha C A B)) :
    lhs ≤ prefactor *
      (count * ((C * C) * (ENNReal.ofReal (2 : Real)) ^ alpha *
        (ENNReal.ofReal (radius : Real)) ^ (2 - alpha))) := by
  exact hmoment.trans (mul_le_mul_right
    (mul_le_mul_right
      (pyzActualCenteredHalfY1FrostmanPieceMass_le_scale_power
        halpha halphaOne hAB hparameter) count)
    prefactor)

#print axioms moment_pieceMass_le_scalePower

end

end FamilyStickyCinematicL32PyzCenteredHalfScaleMomentTransportV1
