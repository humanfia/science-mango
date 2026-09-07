import FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1
import Mathlib.Tactic

/-!
# Literal planar volume of a carrier-coordinate graph strip

The graph may move arbitrarily with the parameter. Tonelli sees only the
length of the parameter interval and the constant vertical width. This is
the quantitative support estimate needed by the canonical low-fibre tail.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8PyzCarrierGraphStripVolumeV1

open FamilyStickyCinematicL32PyzQuasiProductCarrierStripMeasureV1

noncomputable section

theorem volume_pyzCarrierGraphStrip_le
    {a b width : Real} {g : Real → Real}
    (hg : Measurable g) :
    volume (pyzCarrierGraphStrip a b g width) ≤
      ENNReal.ofReal (2 * width) * ENNReal.ofReal (b - a) := by
  have hstrip : MeasurableSet (pyzCarrierGraphStrip a b g width) :=
    measurableSet_pyzCarrierGraphStrip hg
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hstrip]
  calc
    (∫⁻ theta, volume
        ((fun y : Real ↦ (y, theta)) ⁻¹'
          pyzCarrierGraphStrip a b g width) ∂volume) ≤
        ∫⁻ theta, (Icc a b).indicator
          (fun _ ↦ ENNReal.ofReal (2 * width)) theta ∂volume := by
      apply lintegral_mono
      intro theta
      by_cases htheta : theta ∈ Icc a b
      · have hpre :
            (fun y : Real ↦ (y, theta)) ⁻¹'
                pyzCarrierGraphStrip a b g width =
              Icc (g theta - width) (g theta + width) := by
          ext y
          change (theta ∈ Icc a b ∧
              y ∈ Icc (g theta - width) (g theta + width)) ↔
            y ∈ Icc (g theta - width) (g theta + width)
          exact and_iff_right htheta
        change volume
            ((fun y : Real ↦ (y, theta)) ⁻¹'
              pyzCarrierGraphStrip a b g width) ≤ _
        rw [hpre, Set.indicator_of_mem htheta, Real.volume_Icc]
        rw [show g theta + width - (g theta - width) = 2 * width by ring]
      · have hpre :
            (fun y : Real ↦ (y, theta)) ⁻¹'
                pyzCarrierGraphStrip a b g width = ∅ := by
          ext y
          change (theta ∈ Icc a b ∧
              y ∈ Icc (g theta - width) (g theta + width)) ↔ False
          simp [htheta]
        change volume
            ((fun y : Real ↦ (y, theta)) ⁻¹'
              pyzCarrierGraphStrip a b g width) ≤ _
        rw [hpre, measure_empty, Set.indicator_of_notMem htheta]
    _ = ENNReal.ofReal (2 * width) * volume (Icc a b) := by
      exact lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (2 * width) * ENNReal.ofReal (b - a) := by
      rw [Real.volume_Icc]

/-- The canonical `[-2,2]` strip of transverse half-width `3 * tau` has
planar volume at most `24 * tau`. This includes `tau = 0`. -/
theorem volume_pyzCarrierGraphStrip_negTwo_two_three_mul_le
    (tau : NNReal) {g : Real → Real} (hg : Measurable g) :
    volume (pyzCarrierGraphStrip (-2) 2 g (3 * (tau : Real))) ≤
      24 * (tau : ENNReal) := by
  calc
    volume (pyzCarrierGraphStrip (-2) 2 g (3 * (tau : Real))) ≤
        ENNReal.ofReal (2 * (3 * (tau : Real))) *
          ENNReal.ofReal ((2 : Real) - (-2)) :=
      volume_pyzCarrierGraphStrip_le hg
    _ = 24 * (tau : ENNReal) := by
      rw [show 2 * (3 * (tau : Real)) = 6 * (tau : Real) by ring]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 6)]
      norm_num
      ring

#print axioms volume_pyzCarrierGraphStrip_le
#print axioms volume_pyzCarrierGraphStrip_negTwo_two_three_mul_le

end
end Family8PyzCarrierGraphStripVolumeV1
