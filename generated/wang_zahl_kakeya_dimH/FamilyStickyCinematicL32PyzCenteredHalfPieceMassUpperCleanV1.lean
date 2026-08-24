import FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped ENNReal

namespace FamilyStickyCinematicL32PyzCenteredHalfPieceMassUpperCleanV1

open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32PyzActualCenteredHalfY1QuasiProductMassV1

noncomputable section

/-!
# Numerical upper bound for the centered-half quasi-product piece mass

The `J/16` factor in the faithful carrier mass is at most one when the
source parameter interval lies in `[-1,1]`.  This is the first purely
numerical reduction after the actual low-multiplicity moment estimate; it
does not add a geometric or measure-theoretic hypothesis.
-/

theorem centered_sixteenth_width_nonneg_le_one
    {A B : Real} (hAB : A ≤ B)
    (hparameter : ∀ z ∈ Set.Icc A B, |z| ≤ 1) :
    0 ≤ centeredFractionRight A B (1 / 16 : Real) -
        centeredFractionLeft A B (1 / 16 : Real) ∧
      centeredFractionRight A B (1 / 16 : Real) -
        centeredFractionLeft A B (1 / 16 : Real) ≤ 1 := by
  have hA := hparameter A ⟨le_rfl, hAB⟩
  have hB := hparameter B ⟨hAB, le_rfl⟩
  have hAlower : -1 ≤ A := (abs_le.mp hA).1
  have hBupper : B ≤ 1 := (abs_le.mp hB).2
  simp only [centeredFractionLeft, centeredFractionRight]
  constructor <;> linarith

theorem pyzActualCenteredHalfY1FrostmanPieceMass_le_drop_interval
    {radius : NNReal} {alpha : Real} {C : ENNReal} {A B : Real}
    (halpha : 0 ≤ alpha) (hAB : A ≤ B)
    (hparameter : ∀ z ∈ Set.Icc A B, |z| ≤ 1) :
    pyzActualCenteredHalfY1FrostmanPieceMass radius alpha C A B ≤
      (C * (ENNReal.ofReal (radius : Real)) ^ (1 - alpha) *
          (ENNReal.ofReal (2 * (radius : Real))) ^ alpha) *
        (C * (ENNReal.ofReal (radius : Real)) ^ (1 - alpha)) := by
  have hwidth := centered_sixteenth_width_nonneg_le_one hAB hparameter
  have hwidthOfReal :
      ENNReal.ofReal
          (centeredFractionRight A B (1 / 16 : Real) -
            centeredFractionLeft A B (1 / 16 : Real)) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr hwidth.2
  have hwidthRpow :
      (ENNReal.ofReal
          (centeredFractionRight A B (1 / 16 : Real) -
            centeredFractionLeft A B (1 / 16 : Real))) ^ alpha ≤ 1 := by
    simpa only [ENNReal.one_rpow] using
      ENNReal.rpow_le_rpow hwidthOfReal halpha
  have hinner := mul_le_mul_right hwidthRpow
    (C * (ENNReal.ofReal (radius : Real)) ^ (1 - alpha))
  have houter := mul_le_mul_right hinner
    (C * (ENNReal.ofReal (radius : Real)) ^ (1 - alpha) *
      (ENNReal.ofReal (2 * (radius : Real))) ^ alpha)
  simpa only [pyzActualCenteredHalfY1FrostmanPieceMass, mul_one] using houter

#print axioms centered_sixteenth_width_nonneg_le_one
#print axioms pyzActualCenteredHalfY1FrostmanPieceMass_le_drop_interval

end

end FamilyStickyCinematicL32PyzCenteredHalfPieceMassUpperCleanV1
