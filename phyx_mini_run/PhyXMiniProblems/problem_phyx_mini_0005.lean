import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0005

/-- The real-valued readout of a physical length when it is expressed in SI units. -/
def siLengthValue (length : Dimensionful (WithDim Dimension.L𝓭 ℝ)) : ℝ :=
  (length UnitChoices.SI).val

/--
The dimensionful labels in the container cross-section. The coin is at the
midpoint of the bottom segment of length `width`; `height` is the vertical
distance from the bottom to the horizontal fluid surface and viewing rim.
-/
structure ContainerGeometry where
  /-- Figure label `h`, the container height. -/
  height : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  /-- Figure label `d`, the full container width. -/
  width : Dimensionful (WithDim Dimension.L𝓭 ℝ)
  height_pos : 0 < siLengthValue height
  width_pos : 0 < siLengthValue width

/--
Snell's law for a ray leaving a fluid through its horizontal surface into air
of refractive index one. The refractive index is dimensionless, and both angle
readouts are real numbers measured in radians from the surface normal.
-/
def SnellLawAtFluidAirInterface
    (fluidRefractiveIndex airAngleRadians fluidAngleRadians : ℝ) : Prop :=
  fluidRefractiveIndex * Real.sin fluidAngleRadians = Real.sin airAngleRadians

/--
The empty-container figure readout at the fixed viewing angle: the sightline
through the near top rim reaches the far bottom edge, so its horizontal run is
the full width `d` and its vertical run is the height `h`.
-/
def EmptyContainerFarEdgeSightline
    (geometry : ContainerGeometry) (airAngleRadians : ℝ) : Prop :=
  airAngleRadians ∈ Set.Ioo 0 (Real.pi / 2) ∧
    Real.tan airAngleRadians =
      siLengthValue geometry.width / siLengthValue geometry.height

/--
The center of the coin is visible at the same external viewing angle when an
acute ray from the bottom midpoint to the near top rim has the figure-imposed
half-width slope and obeys Snell's law at the fluid--air interface.
-/
def CoinCenterVisibleAtSameViewingAngle
    (geometry : ContainerGeometry)
    (fluidRefractiveIndex airAngleRadians : ℝ) : Prop :=
  ∃ fluidAngleRadians ∈ Set.Ioo 0 (Real.pi / 2),
    Real.tan fluidAngleRadians =
        (siLengthValue geometry.width / 2) / siLengthValue geometry.height ∧
      SnellLawAtFluidAirInterface
        fluidRefractiveIndex airAngleRadians fluidAngleRadians

/--
For every positive container height `h` and width `d`, a fluid whose
dimensionless refractive index is greater than two prevents the midpoint coin
from being visible at the same angle from which the far bottom edge was
visible when the container was empty (answer choice C).

Blueprint: `thm:physics:phyx_mini_0005:target`.
-/
theorem refractiveIndex_gt_two_makes_coinCenter_invisible
    (fluidRefractiveIndex : ℝ)
    (h_index : 2 < fluidRefractiveIndex) :
    ∀ (geometry : ContainerGeometry) (airAngleRadians : ℝ),
      EmptyContainerFarEdgeSightline geometry airAngleRadians →
        ¬ CoinCenterVisibleAtSameViewingAngle
          geometry fluidRefractiveIndex airAngleRadians := by
  intro geometry airAngleRadians h_empty h_visible
  rcases h_empty with ⟨h_air_acute, h_tan_air⟩
  rcases h_visible with
    ⟨fluidAngleRadians, h_fluid_acute, h_tan_fluid, h_snell⟩
  have h_height_ne : siLengthValue geometry.height ≠ 0 :=
    ne_of_gt geometry.height_pos
  have h_tan_relation :
      Real.tan airAngleRadians = 2 * Real.tan fluidAngleRadians := by
    rw [h_tan_air, h_tan_fluid]
    field_simp
  have h_sin_air_pos : 0 < Real.sin airAngleRadians :=
    Real.sin_pos_of_pos_of_lt_pi h_air_acute.1 (by
      linarith [h_air_acute.2, Real.pi_pos])
  have h_sin_fluid_pos : 0 < Real.sin fluidAngleRadians :=
    Real.sin_pos_of_pos_of_lt_pi h_fluid_acute.1 (by
      linarith [h_fluid_acute.2, Real.pi_pos])
  have h_cos_air_pos : 0 < Real.cos airAngleRadians :=
    Real.cos_pos_of_mem_Ioo ⟨by
      linarith [h_air_acute.1, Real.pi_pos], h_air_acute.2⟩
  have h_cos_fluid_pos : 0 < Real.cos fluidAngleRadians :=
    Real.cos_pos_of_mem_Ioo ⟨by
      linarith [h_fluid_acute.1, Real.pi_pos], h_fluid_acute.2⟩
  have h_cross :
      Real.sin airAngleRadians * Real.cos fluidAngleRadians =
        2 * Real.sin fluidAngleRadians * Real.cos airAngleRadians := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos] at h_tan_relation
    field_simp [ne_of_gt h_cos_air_pos, ne_of_gt h_cos_fluid_pos] at h_tan_relation
    nlinarith [h_tan_relation]
  change fluidRefractiveIndex * Real.sin fluidAngleRadians =
    Real.sin airAngleRadians at h_snell
  have h_sin_gt :
      2 * Real.sin fluidAngleRadians < Real.sin airAngleRadians := by
    nlinarith [mul_lt_mul_of_pos_right h_index h_sin_fluid_pos]
  have h_index_cos_relation :
      fluidRefractiveIndex * Real.cos fluidAngleRadians =
        2 * Real.cos airAngleRadians := by
    rw [← h_snell] at h_cross
    apply mul_left_cancel₀ (ne_of_gt h_sin_fluid_pos)
    nlinarith [h_cross]
  have h_cos_gt :
      Real.cos fluidAngleRadians < Real.cos airAngleRadians := by
    nlinarith [mul_lt_mul_of_pos_right h_index h_cos_fluid_pos]
  have h_sin_sq_gt :
      Real.sin fluidAngleRadians ^ 2 < Real.sin airAngleRadians ^ 2 := by
    nlinarith
  have h_cos_sq_gt :
      Real.cos fluidAngleRadians ^ 2 < Real.cos airAngleRadians ^ 2 := by
    nlinarith
  nlinarith [Real.sin_sq_add_cos_sq airAngleRadians,
    Real.sin_sq_add_cos_sq fluidAngleRadians]

end PhyXMiniProblems.ProblemPhyXMini0005
