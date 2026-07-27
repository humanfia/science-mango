import Mathlib.Analysis.Complex.Trigonometric
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026 Problem 2, Part B.2

A half-cylindrical mirror and a fully absorbing cylindrical container have
parallel axes.  This file records the reduced Figure 2f geometry, the ray
conditions, the result of Part B.1, and the projected-width power balance used
to determine the dimensionless ratio `P / P₀`.
-/

namespace IPhO2026Problems
namespace IPhO_2026_2_B_2

open Dimension

/-- A length readout in one fixed coherent unit system. -/
abbrev LengthReadout := WithDim L𝓭 ℝ

/-- The physical dimension mass · length² · time⁻³ of optical power. -/
def opticalPowerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension mass · time⁻³ of irradiance (power per unit area). -/
def irradianceDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- An optical-power readout in the same fixed coherent unit system. -/
abbrev PowerReadout := WithDim opticalPowerDimension ℝ

/-- A solar-irradiance readout in the same fixed coherent unit system. -/
abbrev IrradianceReadout := WithDim irradianceDimension ℝ

/--
The dimensioned quantities and ray observables named in Figure 2f.

The three direction fields are dimensionless coordinate vectors.  The
incidence angle is measured from the mirror normal at the point of incidence.
The common `axialLength` is the illuminated length of both cylinders; it
cancels from the requested power ratio.
-/
structure Figure2fSetup (Ray : Type) where
  mirrorRadius : LengthReadout
  containerRadius : LengthReadout
  centerSeparationInSymmetryPlane : LengthReadout
  axialLength : LengthReadout
  radiusCoefficientAlpha : LengthReadout
  radiusCoefficientBeta : LengthReadout
  thetaMax : ℝ
  solarIrradiance : IrradianceReadout
  receivedPower : PowerReadout
  noMirrorPower : PowerReadout
  actualProjectedWidth : LengthReadout
  noMirrorProjectedWidth : LengthReadout
  mirrorAxisDirection : Fin 3 → ℝ
  containerAxisDirection : Fin 3 → ℝ
  opticalAxisDirection : Fin 3 → ℝ
  incomingDirection : Ray → Fin 3 → ℝ
  rayIrradiance : Ray → IrradianceReadout
  reflectedFromMirror : Ray → Prop
  strikesContainer : Ray → Prop
  absorbedByContainer : Ray → Prop
  mirrorReflectionCount : Ray → ℕ
  incidenceAngleToNormal : Ray → ℝ

/--
The geometric and orientation readouts of Figure 2f.

The existential scalar in `axes_parallel` gives an equation witnessing
parallelism rather than leaving it as an opaque geometric predicate.  The
strict acute-angle branch fixes the physical incidence-angle orientation.
-/
structure Figure2fGeometry {Ray : Type} (s : Figure2fSetup Ray) : Prop where
  mirror_radius_pos : 0 < s.mirrorRadius.val
  container_radius_pos : 0 < s.containerRadius.val
  axial_length_pos : 0 < s.axialLength.val
  center_separation :
    s.centerSeparationInSymmetryPlane.val = s.mirrorRadius.val / 2
  axes_parallel :
    ∃ scale : ℝ, scale ≠ 0 ∧
      s.containerAxisDirection = scale • s.mirrorAxisDirection
  thetaMax_pos : 0 < s.thetaMax
  thetaMax_lt_pi_div_two : s.thetaMax < Real.pi / 2

/--
The reusable conclusion of Part B.1, represented without importing its Lean
output: `a = α sin θ_max + β sin (2 θ_max)`, with `α = R` and `β = -R/2`.
-/
structure PreviousPartB1Result {Ray : Type} (s : Figure2fSetup Ray) : Prop where
  radius_decomposition :
    s.containerRadius.val =
      s.radiusCoefficientAlpha.val * Real.sin s.thetaMax +
        s.radiusCoefficientBeta.val * Real.sin (2 * s.thetaMax)
  alpha_eq_mirror_radius :
    s.radiusCoefficientAlpha.val = s.mirrorRadius.val
  beta_eq_neg_half_mirror_radius :
    s.radiusCoefficientBeta.val = -(s.mirrorRadius.val / 2)

/--
The ray-level assumptions from the problem statement.

Uniform intensity and parallelism are exposed as equalities.  Perfect
absorption and the one-reflection condition are exposed as implications, while
the maximum-angle condition supplies both an upper bound and a limiting ray.
-/
structure ValidFigure2fRayOptics {Ray : Type} (s : Figure2fSetup Ray) : Prop where
  uniform_irradiance :
    ∀ ray, (s.rayIrradiance ray).val = s.solarIrradiance.val
  parallel_to_optical_axis :
    ∀ ray, s.incomingDirection ray = s.opticalAxisDirection
  fully_absorbing :
    ∀ ray, s.strikesContainer ray → s.absorbedByContainer ray
  absorbed_after_at_most_one_reflection :
    ∀ ray, s.absorbedByContainer ray → s.mirrorReflectionCount ray ≤ 1
  reflected_incidence_nonnegative :
    ∀ ray, s.reflectedFromMirror ray → s.strikesContainer ray →
      0 ≤ s.incidenceAngleToNormal ray
  thetaMax_is_upper_bound :
    ∀ ray, s.reflectedFromMirror ray → s.strikesContainer ray →
      s.incidenceAngleToNormal ray ≤ s.thetaMax
  thetaMax_is_attained :
    ∃ ray, s.reflectedFromMirror ray ∧ s.strikesContainer ray ∧
      s.incidenceAngleToNormal ray = s.thetaMax

/--
Power accounting for constant uniform irradiance.

The two width equations are the Figure 2f projected-aperture readouts.  The two
power equations state that a fully absorbed parallel beam carries irradiance
times projected area, with the common projected area written as width times
axial length.  None of these fields states the requested final ratio.
-/
structure Figure2fPowerBalance {Ray : Type} (s : Figure2fSetup Ray) : Prop where
  irradiance_pos : 0 < s.solarIrradiance.val
  no_mirror_projected_width :
    s.noMirrorProjectedWidth.val = 2 * s.containerRadius.val
  actual_projected_width :
    s.actualProjectedWidth.val =
      2 * s.mirrorRadius.val * Real.sin s.thetaMax
  no_mirror_power_balance :
    s.noMirrorPower.val =
      s.solarIrradiance.val * s.noMirrorProjectedWidth.val * s.axialLength.val
  actual_power_balance :
    s.receivedPower.val =
      s.solarIrradiance.val * s.actualProjectedWidth.val * s.axialLength.val

/--
Part B.1 and the double-angle identity rewrite the container radius in a form
that displays the factor which will cancel against the collected aperture.
-/
theorem container_radius_factorization {Ray : Type} (s : Figure2fSetup Ray)
    (hB1 : PreviousPartB1Result s) :
    s.containerRadius.val =
      s.mirrorRadius.val * Real.sin s.thetaMax *
        (1 - Real.cos s.thetaMax) := by
  calc
    s.containerRadius.val =
        s.radiusCoefficientAlpha.val * Real.sin s.thetaMax +
          s.radiusCoefficientBeta.val * Real.sin (2 * s.thetaMax) :=
      hB1.radius_decomposition
    _ = s.mirrorRadius.val * Real.sin s.thetaMax *
        (1 - Real.cos s.thetaMax) := by
      rw [hB1.alpha_eq_mirror_radius, hB1.beta_eq_neg_half_mirror_radius,
        Real.sin_two_mul]
      ring

/--
The common irradiance and axial extent cancel, so the power ratio equals the
ratio of the two projected widths.
-/
theorem power_ratio_eq_projected_width_ratio {Ray : Type} (s : Figure2fSetup Ray)
    (hGeometry : Figure2fGeometry s) (hPower : Figure2fPowerBalance s) :
    s.receivedPower.val / s.noMirrorPower.val =
      s.actualProjectedWidth.val / s.noMirrorProjectedWidth.val := by
  have hIrradiance_ne : s.solarIrradiance.val ≠ 0 :=
    ne_of_gt hPower.irradiance_pos
  have hAxialLength_ne : s.axialLength.val ≠ 0 :=
    ne_of_gt hGeometry.axial_length_pos
  have hNoMirrorWidth_ne : s.noMirrorProjectedWidth.val ≠ 0 := by
    rw [hPower.no_mirror_projected_width]
    exact mul_ne_zero (by norm_num) (ne_of_gt hGeometry.container_radius_pos)
  have hNoMirrorPower_ne : s.noMirrorPower.val ≠ 0 := by
    rw [hPower.no_mirror_power_balance]
    exact mul_ne_zero (mul_ne_zero hIrradiance_ne hNoMirrorWidth_ne)
      hAxialLength_ne
  apply (div_eq_div_iff hNoMirrorPower_ne hNoMirrorWidth_ne).2
  rw [hPower.actual_power_balance, hPower.no_mirror_power_balance]
  ring

/--
For the Figure 2f solar cooker, the actual-to-no-mirror received-power ratio is
`1 / (1 - cos θ_max)`.
-/
theorem power_ratio_eq_one_div_one_sub_cos {Ray : Type} (s : Figure2fSetup Ray)
    (hGeometry : Figure2fGeometry s)
    (hB1 : PreviousPartB1Result s)
    (hRays : ValidFigure2fRayOptics s)
    (hPower : Figure2fPowerBalance s) :
    s.receivedPower.val / s.noMirrorPower.val =
      1 / (1 - Real.cos s.thetaMax) := by
  have hTheta_lt_pi : s.thetaMax < Real.pi :=
    hGeometry.thetaMax_lt_pi_div_two.trans
      (half_lt_self Real.pi_pos)
  have hSin_pos : 0 < Real.sin s.thetaMax :=
    Real.sin_pos_of_pos_of_lt_pi hGeometry.thetaMax_pos hTheta_lt_pi
  have hCommon_ne :
      2 * s.mirrorRadius.val * Real.sin s.thetaMax ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (ne_of_gt hGeometry.mirror_radius_pos))
      (ne_of_gt hSin_pos)
  calc
    s.receivedPower.val / s.noMirrorPower.val =
        s.actualProjectedWidth.val / s.noMirrorProjectedWidth.val :=
      power_ratio_eq_projected_width_ratio s hGeometry hPower
    _ = (2 * s.mirrorRadius.val * Real.sin s.thetaMax) /
        (2 * (s.mirrorRadius.val * Real.sin s.thetaMax *
          (1 - Real.cos s.thetaMax))) := by
      rw [hPower.actual_projected_width, hPower.no_mirror_projected_width,
        container_radius_factorization s hB1]
    _ = (2 * s.mirrorRadius.val * Real.sin s.thetaMax) /
        ((2 * s.mirrorRadius.val * Real.sin s.thetaMax) *
          (1 - Real.cos s.thetaMax)) := by
      congr 1
      ring
    _ = 1 / (1 - Real.cos s.thetaMax) := by
      simpa only [mul_one] using
        (mul_div_mul_left (1 : ℝ) (1 - Real.cos s.thetaMax) hCommon_ne)

end IPhO_2026_2_B_2
end IPhO2026Problems
