import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# IPhO 2026, theoretical problem 2, part B.3

This file models the solar-cooker geometry shown in Figure 2f.  Lengths,
radiant powers, and irradiances are dimensionful quantities; their numerical
values below are explicitly read in SI units.
-/

namespace IPhO2026Problem2B3

noncomputable section

/-- The physical dimension of radiant power, `mass * length² / time³`. -/
def radiantPowerDimension : Dimension :=
  Dimension.M𝓭 * Dimension.L𝓭 ^ (2 : ℕ) * (Dimension.T𝓭 ^ (3 : ℕ))⁻¹

/-- The physical dimension of irradiance, `power / area = mass / time³`. -/
def irradianceDimension : Dimension :=
  Dimension.M𝓭 * (Dimension.T𝓭 ^ (3 : ℕ))⁻¹

/-- A unit-independent physical length. -/
def LengthQuantity := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- A unit-independent physical radiant power. -/
def RadiantPowerQuantity :=
  Dimensionful (WithDim radiantPowerDimension ℝ)

/-- A unit-independent physical irradiance. -/
def IrradianceQuantity :=
  Dimensionful (WithDim irradianceDimension ℝ)

/-- The numerical value of a length in metres (the SI length unit). -/
def lengthInMetres (x : LengthQuantity) : ℝ :=
  (x.1 UnitChoices.SI).val

/-- The numerical value of a length in centimetres. -/
def lengthInCentimetres (x : LengthQuantity) : ℝ :=
  100 * lengthInMetres x

/-- The numerical value of a radiant power in SI units (watts). -/
def powerInWatts (p : RadiantPowerQuantity) : ℝ :=
  (p.1 UnitChoices.SI).val

/-- The numerical value of an irradiance in SI units (`W / m²`). -/
def irradianceInSI (i : IrradianceQuantity) : ℝ :=
  (i.1 UnitChoices.SI).val

/--
The named physical data of the solar cooker in Figure 2f.

Directions are dimensionless vectors in three-dimensional space.  They are
chosen with consistent orientations, so equality of direction representatives
encodes the parallelism stated in the problem.
-/
structure SolarCooker where
  mirrorRadius : LengthQuantity
  containerRadius : LengthQuantity
  containerCenterOffset : LengthQuantity
  containerCenterOutOfSymmetryPlane : LengthQuantity
  mirrorApertureWidth : LengthQuantity
  mirrorAngularExtent : ℝ
  mirrorAxisDirection : Fin 3 → ℝ
  containerAxisDirection : Fin 3 → ℝ
  opticalAxisDirection : Fin 3 → ℝ
  sunlightRayDirection : Fin 3 → ℝ
  uniformSolarIrradiance : IrradianceQuantity
  containerAbsorptivity : ℝ
  maxReflectionsForAbsorbedRay : ℕ
  /-- Largest normal-referenced mirror-incidence angle of a reflected ray
  which strikes the container. -/
  thetaMax : ℝ

/--
The figure-derived geometry and operating regime stated in the problem.
Every substantive geometric or optical assertion is exposed as an equation or
inequality rather than hidden in an opaque predicate.
-/
structure Figure2fAssumptions (cooker : SolarCooker) : Prop where
  mirrorRadius_positive : 0 < lengthInMetres cooker.mirrorRadius
  containerRadius_positive : 0 < lengthInMetres cooker.containerRadius
  mirror_is_half_cylinder : cooker.mirrorAngularExtent = Real.pi
  aperture_width_eq_two_radii :
    lengthInMetres cooker.mirrorApertureWidth =
      2 * lengthInMetres cooker.mirrorRadius
  container_center_offset_eq_half_radius :
    lengthInMetres cooker.containerCenterOffset =
      lengthInMetres cooker.mirrorRadius / 2
  container_center_on_symmetry_plane :
    lengthInMetres cooker.containerCenterOutOfSymmetryPlane = 0
  mirror_axis_direction_is_unit :
    ∑ i : Fin 3, cooker.mirrorAxisDirection i ^ 2 = 1
  optical_axis_direction_is_unit :
    ∑ i : Fin 3, cooker.opticalAxisDirection i ^ 2 = 1
  cylinder_axes_parallel :
    cooker.containerAxisDirection = cooker.mirrorAxisDirection
  sunlight_parallel_to_optical_axis :
    cooker.sunlightRayDirection = cooker.opticalAxisDirection
  sunlight_intensity_positive :
    0 < irradianceInSI cooker.uniformSolarIrradiance
  container_fully_absorbing : cooker.containerAbsorptivity = 1
  absorbed_ray_reflects_at_most_once :
    cooker.maxReflectionsForAbsorbedRay ≤ 1
  thetaMax_nonnegative : 0 ≤ cooker.thetaMax
  thetaMax_le_pi_div_two : cooker.thetaMax ≤ Real.pi / 2

/--
The reusable conclusions of parts B.1 and B.2, restated locally because this
lane must not import sibling problem files.

The first equation is the Figure 2f cutoff-ray geometry.  The second is the
received-power law for uniform parallel illumination and a fully absorbing
container in the one-reflection regime.
-/
structure PreviousPartResults
    (cooker : SolarCooker)
    (actualPower baselinePower : RadiantPowerQuantity) : Prop where
  radius_from_cutoff_ray :
    lengthInMetres cooker.containerRadius =
      lengthInMetres cooker.mirrorRadius * Real.sin cooker.thetaMax -
        (lengthInMetres cooker.mirrorRadius / 2) *
          Real.sin (2 * cooker.thetaMax)
  power_ratio_from_cutoff_angle :
    powerInWatts actualPower / powerInWatts baselinePower =
      1 / (1 - Real.cos cooker.thetaMax)

/--
At a fivefold power gain over a positive baseline, the B.2 power law forces
`cos θ_max = 4/5`.
-/
theorem cosine_thetaMax_of_fivefold_power
    (cooker : SolarCooker)
    (actualPower baselinePower : RadiantPowerQuantity)
    (previous : PreviousPartResults cooker actualPower baselinePower)
    (baselinePower_positive : 0 < powerInWatts baselinePower)
    (fivefold_power :
      powerInWatts actualPower = 5 * powerInWatts baselinePower) :
    Real.cos cooker.thetaMax = (4 : ℝ) / 5 := by
  have hbase_ne : powerInWatts baselinePower ≠ 0 :=
    ne_of_gt baselinePower_positive
  have h : (5 : ℝ) = 1 / (1 - Real.cos cooker.thetaMax) := by
    calc
      (5 : ℝ) =
          powerInWatts actualPower / powerInWatts baselinePower := by
        rw [fivefold_power]
        field_simp
      _ = 1 / (1 - Real.cos cooker.thetaMax) :=
        previous.power_ratio_from_cutoff_angle
  have hden : 1 - Real.cos cooker.thetaMax ≠ 0 := by
    intro hzero
    rw [hzero] at h
    norm_num at h
  field_simp [hden] at h
  linarith

/--
Using both previous-part laws and the nonnegative incidence-angle branch,
`R = 1 m` together with a fivefold power gain forces the requested container
radius.
-/
theorem container_radius_of_fivefold_power
    (cooker : SolarCooker)
    (actualPower baselinePower : RadiantPowerQuantity)
    (figure : Figure2fAssumptions cooker)
    (previous : PreviousPartResults cooker actualPower baselinePower)
    (mirrorRadius_eq_one_metre :
      lengthInMetres cooker.mirrorRadius = 1)
    (baselinePower_positive : 0 < powerInWatts baselinePower)
    (fivefold_power :
      powerInWatts actualPower = 5 * powerInWatts baselinePower) :
    lengthInMetres cooker.containerRadius = (12 : ℝ) / 100 ∧
      lengthInCentimetres cooker.containerRadius = 12 := by
  have hcos : Real.cos cooker.thetaMax = (4 : ℝ) / 5 :=
    cosine_thetaMax_of_fivefold_power cooker actualPower baselinePower previous
      baselinePower_positive fivefold_power
  have htheta_le_pi : cooker.thetaMax ≤ Real.pi := by
    nlinarith [figure.thetaMax_le_pi_div_two, Real.pi_pos]
  have hsin_nonneg : 0 ≤ Real.sin cooker.thetaMax :=
    Real.sin_nonneg_of_nonneg_of_le_pi figure.thetaMax_nonnegative htheta_le_pi
  have htrig := Real.sin_sq_add_cos_sq cooker.thetaMax
  have hsin : Real.sin cooker.thetaMax = (3 : ℝ) / 5 := by
    rw [hcos] at htrig
    nlinarith
  have hsin_two : Real.sin (2 * cooker.thetaMax) = (24 : ℝ) / 25 := by
    rw [Real.sin_two_mul, hsin, hcos]
    norm_num
  have hradius := previous.radius_from_cutoff_ray
  rw [mirrorRadius_eq_one_metre, hsin, hsin_two] at hradius
  constructor
  · norm_num at hradius ⊢
    exact hradius
  · rw [lengthInCentimetres, hradius]
    norm_num

/--
Answer to IPhO 2026 theoretical problem 2, part B.3: the operating point has
`cos θ_max = 4/5`, and the required radius is `0.12 m = 12 cm`.
-/
theorem ipho2026_problem2_B3
    (cooker : SolarCooker)
    (actualPower baselinePower : RadiantPowerQuantity)
    (figure : Figure2fAssumptions cooker)
    (previous : PreviousPartResults cooker actualPower baselinePower)
    (mirrorRadius_eq_one_metre :
      lengthInMetres cooker.mirrorRadius = 1)
    (baselinePower_positive : 0 < powerInWatts baselinePower)
    (fivefold_power :
      powerInWatts actualPower = 5 * powerInWatts baselinePower) :
    Real.cos cooker.thetaMax = (4 : ℝ) / 5 ∧
      lengthInMetres cooker.containerRadius = (12 : ℝ) / 100 ∧
      lengthInCentimetres cooker.containerRadius = 12 := by
  constructor
  · exact
      cosine_thetaMax_of_fivefold_power cooker actualPower baselinePower previous
        baselinePower_positive fivefold_power
  · exact
      container_radius_of_fivefold_power cooker actualPower baselinePower figure previous
        mirrorRadius_eq_one_metre baselinePower_positive fivefold_power

end

end IPhO2026Problem2B3
