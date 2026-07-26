import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/- USER: The source file did not exist when this autoformalization task began. -/

namespace PhyXMiniProblems
namespace ProblemPhyXMini0023

noncomputable section

open Dimension

/-- A real-valued length whose dimension is tracked by PhysLean. -/
abbrev DimLengthReal := Dimensionful (WithDim L𝓭 ℝ)

/-- A real-valued duration whose dimension is tracked by PhysLean. -/
abbrev DimTimeReal := Dimensionful (WithDim T𝓭 ℝ)

/-- A real-valued speed whose dimension is tracked by PhysLean. -/
abbrev DimSpeedReal := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Unit choices in which length is read in centimeters and all other units are SI. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- Unit choices in which time is read in nanoseconds and all other units are SI. -/
def nanosecondUnitChoices : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.nanoseconds }

/-- Convert a scalar degree readout to the radian value used by `Real.sin`. -/
def degrees (angleDegrees : ℝ) : ℝ := angleDegrees * Real.pi / 180

/-- The refractive index of the surrounding air in the idealized problem model. -/
def airRefractiveIndex : ℝ := 1

/-- A rectangular plastic block, represented by its dimensionless refractive index. -/
structure RectangularPlasticBlock where
  /-- Refractive-index readout `n` from the figure. -/
  refractiveIndex : ℝ
  /-- Ordinary plastic is optically denser than the surrounding air. -/
  refractiveIndex_gt_air : airRefractiveIndex < refractiveIndex

/-- Absolute scalar tolerance, used to state the precision of a displayed answer choice. -/
def WithinAbsoluteTolerance (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| ≤ tolerance

/-- The four displayed transit-time choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq

/-- The nanosecond readout printed next to an answer choice. -/
def AnswerChoice.timeNanoseconds : AnswerChoice → ℝ
  | .A => 285 / 100
  | .B => 391 / 100
  | .C => 340 / 100
  | .D => 412 / 100

/-- A dimensionful time agrees with a displayed choice to its hundredth-nanosecond precision. -/
def MatchesAnswerChoice (travelTime : DimTimeReal) (choice : AnswerChoice) : Prop :=
  WithinAbsoluteTolerance
    (travelTime nanosecondUnitChoices).val choice.timeNanoseconds (5 / 1000)

/--
The governing physical laws for the ray shown in the figure.

`entryAngle` is measured from the horizontal normal to the left face, `internalAngle`
is the corresponding angle inside the block, `bottomIncidenceAngle` is measured from
the vertical normal to the bottom face, and `exitAngle` is the outgoing angle from
that normal.  The scalar equations involving dimensional quantities are their SI
readouts.
-/
structure RectangularBlockTransitLaws
    (block : RectangularPlasticBlock)
    (entryAngle internalAngle bottomIncidenceAngle exitAngle : ℝ)
    (entryDrop internalPathLength : DimLengthReal)
    (plasticSpeed : DimSpeedReal)
    (travelTime : DimTimeReal) : Prop where
  /-- The normals of adjacent faces of a rectangle are perpendicular. -/
  adjacentFaceNormals : bottomIncidenceAngle = Real.pi / 2 - internalAngle
  /-- Snell's law at the left air-plastic interface. -/
  snellAtEntry :
    airRefractiveIndex * Real.sin entryAngle =
      block.refractiveIndex * Real.sin internalAngle
  /-- Snell's law at the bottom plastic-air interface. -/
  snellAtExit :
    block.refractiveIndex * Real.sin bottomIncidenceAngle =
      airRefractiveIndex * Real.sin exitAngle
  /-- The vertical component of the internal path is the figure distance `L`. -/
  pathGeometry :
    (internalPathLength UnitChoices.SI).val * Real.sin internalAngle =
      (entryDrop UnitChoices.SI).val
  /-- Light travels in the plastic at vacuum speed divided by its refractive index. -/
  speedInPlastic :
    (plasticSpeed UnitChoices.SI).val * block.refractiveIndex =
      (DimSpeed.speedOfLight UnitChoices.SI).val
  /-- Constant-speed travel relates the path length, speed, and elapsed time. -/
  travelKinematics :
    (travelTime UnitChoices.SI).val * (plasticSpeed UnitChoices.SI).val =
      (internalPathLength UnitChoices.SI).val

/--
For the rectangular-block ray diagram with `θ₁ = 45°`, `θ₂ = 76°`, and
`L = 50 cm`, the transit time rounds to answer choice C, `3.40 ns`.

The tolerance `0.005 ns` is half a unit in the last displayed decimal place.

Blueprint: `thm:physics:phyx_mini_0023:target`.
-/
theorem travel_time_through_rectangular_plastic_block
    (block : RectangularPlasticBlock)
    (entryAngle internalAngle bottomIncidenceAngle exitAngle : ℝ)
    (entryDrop internalPathLength : DimLengthReal)
    (plasticSpeed : DimSpeedReal)
    (travelTime : DimTimeReal)
    (h_entryAngle : entryAngle = degrees 45)
    (h_exitAngle : exitAngle = degrees 76)
    (h_entryDrop : entryDrop centimeterUnitChoices = ⟨50⟩)
    (h_internalAngle : 0 < internalAngle ∧ internalAngle < Real.pi / 2)
    (h_bottomIncidenceAngle :
      0 < bottomIncidenceAngle ∧ bottomIncidenceAngle < Real.pi / 2)
    (h_internalPathLength : 0 < (internalPathLength UnitChoices.SI).val)
    (h_plasticSpeed : 0 < (plasticSpeed UnitChoices.SI).val)
    (h_travelTime : 0 ≤ (travelTime UnitChoices.SI).val)
    (laws : RectangularBlockTransitLaws block entryAngle internalAngle
      bottomIncidenceAngle exitAngle entryDrop internalPathLength plasticSpeed travelTime) :
    MatchesAnswerChoice travelTime .C := by
  have h_entry_units :
      (entryDrop centimeterUnitChoices).val =
        100 * (entryDrop UnitChoices.SI).val := by
    have h := congrArg WithDim.val <| entryDrop.property
      UnitChoices.SI centimeterUnitChoices
    norm_num [centimeterUnitChoices, UnitChoices.dimScale,
      LengthUnit.centimeters, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val, NNReal.toReal] at h ⊢
    exact h
  have h_entryDrop_cm :
      (entryDrop centimeterUnitChoices).val = 50 := by
    exact congrArg WithDim.val h_entryDrop
  have h_entryDrop_SI :
      (entryDrop UnitChoices.SI).val = (1 / 2 : ℝ) := by
    nlinarith
  have h_time_units :
      (travelTime nanosecondUnitChoices).val =
        1000000000 * (travelTime UnitChoices.SI).val := by
    have h := congrArg WithDim.val <| travelTime.property
      UnitChoices.SI nanosecondUnitChoices
    norm_num [nanosecondUnitChoices, UnitChoices.dimScale,
      TimeUnit.nanoseconds, TimeUnit.seconds, TimeUnit.scale,
      TimeUnit.div_eq_val, NNReal.toReal] at h ⊢
    exact h
  have h_snell_entry :
      Real.sin entryAngle =
        block.refractiveIndex * Real.sin internalAngle := by
    simpa [airRefractiveIndex] using laws.snellAtEntry
  have h_snell_exit :
      block.refractiveIndex * Real.cos internalAngle =
        Real.sin exitAngle := by
    have h := laws.snellAtExit
    rw [laws.adjacentFaceNormals, Real.sin_pi_div_two_sub] at h
    simpa [airRefractiveIndex] using h
  have h_index_sq :
      block.refractiveIndex ^ 2 =
        Real.sin entryAngle ^ 2 + Real.sin exitAngle ^ 2 := by
    calc
      block.refractiveIndex ^ 2 =
          block.refractiveIndex ^ 2 *
            (Real.sin internalAngle ^ 2 + Real.cos internalAngle ^ 2) := by
              rw [Real.sin_sq_add_cos_sq, mul_one]
      _ = (block.refractiveIndex * Real.sin internalAngle) ^ 2 +
          (block.refractiveIndex * Real.cos internalAngle) ^ 2 := by ring
      _ = Real.sin entryAngle ^ 2 + Real.sin exitAngle ^ 2 := by
        rw [← h_snell_entry, h_snell_exit]
  have h_time_path :
      (travelTime UnitChoices.SI).val *
          (DimSpeed.speedOfLight UnitChoices.SI).val *
          Real.sin internalAngle =
        block.refractiveIndex * (entryDrop UnitChoices.SI).val := by
    calc
      (travelTime UnitChoices.SI).val *
            (DimSpeed.speedOfLight UnitChoices.SI).val *
            Real.sin internalAngle =
          (travelTime UnitChoices.SI).val *
            (plasticSpeed UnitChoices.SI).val *
            block.refractiveIndex * Real.sin internalAngle := by
              rw [← laws.speedInPlastic]
              ring
      _ = (internalPathLength UnitChoices.SI).val *
            block.refractiveIndex * Real.sin internalAngle := by
              rw [laws.travelKinematics]
      _ = block.refractiveIndex *
            ((internalPathLength UnitChoices.SI).val *
              Real.sin internalAngle) := by ring
      _ = block.refractiveIndex * (entryDrop UnitChoices.SI).val := by
        rw [laws.pathGeometry]
  have h_time_exact :
      (travelTime UnitChoices.SI).val *
          (DimSpeed.speedOfLight UnitChoices.SI).val *
          Real.sin entryAngle =
        (entryDrop UnitChoices.SI).val * block.refractiveIndex ^ 2 := by
    calc
      (travelTime UnitChoices.SI).val *
            (DimSpeed.speedOfLight UnitChoices.SI).val *
            Real.sin entryAngle =
          block.refractiveIndex *
            ((travelTime UnitChoices.SI).val *
              (DimSpeed.speedOfLight UnitChoices.SI).val *
              Real.sin internalAngle) := by
                rw [h_snell_entry]
                ring
      _ = block.refractiveIndex *
            (block.refractiveIndex * (entryDrop UnitChoices.SI).val) := by
              rw [h_time_path]
      _ = (entryDrop UnitChoices.SI).val * block.refractiveIndex ^ 2 := by ring
  have h_entry_radians : entryAngle = Real.pi / 4 := by
    rw [h_entryAngle]
    unfold degrees
    ring
  have h_exit_radians : exitAngle = Real.pi / 2 - 7 * Real.pi / 90 := by
    rw [h_exitAngle]
    unfold degrees
    ring
  rw [h_index_sq, h_entry_radians, Real.sin_pi_div_four, h_exit_radians,
    Real.sin_pi_div_two_sub, DimSpeed.speedOfLight_in_SI, h_entryDrop_SI]
    at h_time_exact
  have hr2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2_lower : (1.4142 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr2_upper : Real.sqrt 2 < (1.4143 : ℝ) := by
    nlinarith only [hr2_sq, hr2_nonneg]
  have hr3_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by
    positivity
  have hr3_sq :
      (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt hr3_arg
  have hr3_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_nonneg _
  have hr3_lower : (1.8477 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hr3_sq, hr3_nonneg, hr2_lower]
  have hr3_upper : Real.sqrt (2 + Real.sqrt 2) < (1.8478 : ℝ) := by
    nlinarith only [hr3_sq, hr3_nonneg, hr2_upper]
  have hr16_arg :
      0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt 2) := by
    linarith only [hr3_upper]
  have hr16_sq :
      (Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt hr16_arg
  have hr16_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have hr16_lower :
      (0.3901 : ℝ) < Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [hr16_sq, hr16_nonneg, hr3_upper]
  have hr16_upper :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) < (0.3903 : ℝ) := by
    nlinarith only [hr16_sq, hr16_nonneg, hr3_lower]
  have hsin16_lower : (0.19505 : ℝ) < Real.sin (Real.pi / 16) := by
    rw [Real.sin_pi_div_sixteen]
    linarith only [hr16_lower]
  have hsin16_upper : Real.sin (Real.pi / 16) < (0.19515 : ℝ) := by
    rw [Real.sin_pi_div_sixteen]
    linarith only [hr16_upper]
  have hx16_nonneg : 0 ≤ Real.pi / 16 := by
    positivity
  have hx16_le_quarter : Real.pi / 16 ≤ (1 / 4 : ℝ) := by
    nlinarith only [Real.pi_le_four]
  have hx16_abs : |Real.pi / 16| ≤ 1 := by
    rw [abs_of_nonneg hx16_nonneg]
    linarith only [hx16_le_quarter]
  have hsin16_approx := Real.sin_bound hx16_abs
  have hsin16_approx_lower := (abs_le.mp hsin16_approx).1
  have hsin16_approx_upper := (abs_le.mp hsin16_approx).2
  rw [abs_of_nonneg hx16_nonneg] at hsin16_approx_lower hsin16_approx_upper
  have hsin16_le_cubic :
      Real.sin (Real.pi / 16) ≤
        Real.pi / 16 - (Real.pi / 16) ^ 3 / 6 +
          (Real.pi / 16) ^ 4 * (5 / 96) := by
    linarith only [hsin16_approx_upper]
  have hsin16_ge_cubic :
      Real.pi / 16 - (Real.pi / 16) ^ 3 / 6 -
          (Real.pi / 16) ^ 4 * (5 / 96) ≤
        Real.sin (Real.pi / 16) := by
    linarith only [hsin16_approx_lower]
  have hx16_cube_le_quarter :
      (Real.pi / 16) ^ 3 ≤ (1 / 4 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx16_nonneg hx16_le_quarter 3
  have hx16_fourth_le_quarter :
      (Real.pi / 16) ^ 4 ≤ (1 / 4 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx16_nonneg hx16_le_quarter 4
  have herror16_le_quarter :
      (Real.pi / 16) ^ 4 * (5 / 96) ≤
        (1 / 4 : ℝ) ^ 4 * (5 / 96) := by
    nlinarith only [hx16_fourth_le_quarter]
  have hpi_lower_coarse : (3 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3 : ℝ) := le_of_not_gt h
    have hx16_cube_nonneg : 0 ≤ (Real.pi / 16) ^ 3 := by
      positivity
    linarith only [hsin16_lower, hsin16_le_cubic,
      herror16_le_quarter, hpi_le, hx16_cube_nonneg]
  have hx16_cube_lower :
      (3 / 16 : ℝ) ^ 3 ≤ (Real.pi / 16) ^ 3 := by
    apply pow_le_pow_left₀ (by norm_num) (by
      linarith only [hpi_lower_coarse]) 3
  have hpi_lower : (3.13 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.13 : ℝ) := le_of_not_gt h
    have hx16_fourth_le :
        (Real.pi / 16) ^ 4 ≤ (3.13 / 16 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hx16_nonneg (by
        linarith only [hpi_le]) 4
    have herror16_le :
        (Real.pi / 16) ^ 4 * (5 / 96) ≤
          (3.13 / 16 : ℝ) ^ 4 * (5 / 96) := by
      nlinarith only [hx16_fourth_le]
    linarith only [hsin16_lower, hsin16_le_cubic, hx16_cube_lower,
      herror16_le, hpi_le]
  have hpi_upper_coarse : Real.pi < (3.2 : ℝ) := by
    by_contra h
    have hpi_ge : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hcube16_term_le :
        (Real.pi / 16) ^ 3 / 6 ≤ (1 / 4 : ℝ) ^ 3 / 6 := by
      nlinarith only [hx16_cube_le_quarter]
    linarith only [hsin16_upper, hsin16_ge_cubic,
      hcube16_term_le, herror16_le_quarter, hpi_ge]
  have hx16_le_fifth : Real.pi / 16 ≤ (1 / 5 : ℝ) := by
    linarith only [hpi_upper_coarse]
  have hx16_cube_le_fifth :
      (Real.pi / 16) ^ 3 ≤ (1 / 5 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx16_nonneg hx16_le_fifth 3
  have hx16_fourth_le_fifth :
      (Real.pi / 16) ^ 4 ≤ (1 / 5 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx16_nonneg hx16_le_fifth 4
  have hcube16_term_le_fifth :
      (Real.pi / 16) ^ 3 / 6 ≤ (1 / 5 : ℝ) ^ 3 / 6 := by
    nlinarith only [hx16_cube_le_fifth]
  have herror16_le_fifth :
      (Real.pi / 16) ^ 4 * (5 / 96) ≤
        (1 / 5 : ℝ) ^ 4 * (5 / 96) := by
    nlinarith only [hx16_fourth_le_fifth]
  have hpi_upper : Real.pi < (3.15 : ℝ) := by
    by_contra h
    have hpi_ge : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt h
    linarith only [hsin16_upper, hsin16_ge_cubic,
      hcube16_term_le_fifth, herror16_le_fifth, hpi_ge]
  let x : ℝ := 7 * Real.pi / 90
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx_upper : x ≤ (0.245 : ℝ) := by
    dsimp [x]
    linarith only [hpi_upper]
  have hx_lower : (7 * 3.13 / 90 : ℝ) ≤ x := by
    dsimp [x]
    linarith only [hpi_lower]
  have hx_abs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx_nonneg]
    linarith only [hx_upper]
  have hcos_approx := Real.cos_bound hx_abs
  have hcos_approx_lower := (abs_le.mp hcos_approx).1
  have hcos_approx_upper := (abs_le.mp hcos_approx).2
  rw [abs_of_nonneg hx_nonneg] at hcos_approx_lower hcos_approx_upper
  have hcos_ge :
      1 - x ^ 2 / 2 - x ^ 4 * (5 / 96) ≤ Real.cos x := by
    linarith only [hcos_approx_lower]
  have hcos_le :
      Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96) := by
    linarith only [hcos_approx_upper]
  have hx_sq_upper : x ^ 2 ≤ (0.245 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hx_nonneg hx_upper 2
  have hx_fourth_upper : x ^ 4 ≤ (0.245 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx_nonneg hx_upper 4
  have hx_sq_lower : (7 * 3.13 / 90 : ℝ) ^ 2 ≤ x ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hx_lower 2
  have hcos_lower :
      (0.9697 : ℝ) < Real.cos (7 * Real.pi / 90) := by
    change (0.9697 : ℝ) < Real.cos x
    linarith only [hcos_ge, hx_sq_upper, hx_fourth_upper]
  have hcos_upper :
      Real.cos (7 * Real.pi / 90) < (0.9706 : ℝ) := by
    change Real.cos x < (0.9706 : ℝ)
    linarith only [hcos_le, hx_sq_lower, hx_fourth_upper]
  let s : ℝ := Real.sqrt 2 / 2
  let q : ℝ := Real.cos (7 * Real.pi / 90)
  have hs_sq : s ^ 2 = (1 / 2 : ℝ) := by
    dsimp [s]
    nlinarith only [hr2_sq]
  have hs_lower : (0.7071 : ℝ) < s := by
    dsimp [s]
    linarith only [hr2_lower]
  have hs_upper : s < (0.70715 : ℝ) := by
    dsimp [s]
    linarith only [hr2_upper]
  have hq_lower : (0.9697 : ℝ) < q := hcos_lower
  have hq_upper : q < (0.9706 : ℝ) := hcos_upper
  have hq_sq_lower : (0.9697 : ℝ) ^ 2 < q ^ 2 :=
    pow_lt_pow_left₀ hq_lower (by norm_num) (by norm_num)
  have hq_sq_upper : q ^ 2 < (0.9706 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hq_upper (by
      linarith only [hq_lower]) (by norm_num)
  have h_scaled :
      (1000000000 * (travelTime UnitChoices.SI).val) *
          (299792458 * s) =
        500000000 * (s ^ 2 + q ^ 2) := by
    dsimp [s, q] at h_time_exact ⊢
    nlinarith only [h_time_exact]
  have hcoeff_pos : 0 < 299792458 * s := by
    positivity
  have h_lower_comparison :
      (3.395 : ℝ) * (299792458 * s) <
        500000000 * (s ^ 2 + q ^ 2) := by
    rw [hs_sq]
    nlinarith only [hs_upper, hq_sq_lower]
  have h_upper_comparison :
      500000000 * (s ^ 2 + q ^ 2) <
        (3.405 : ℝ) * (299792458 * s) := by
    rw [hs_sq]
    nlinarith only [hs_lower, hq_sq_upper]
  have h_time_ns_lower :
      (3.395 : ℝ) <
        1000000000 * (travelTime UnitChoices.SI).val := by
    apply lt_of_mul_lt_mul_right _ hcoeff_pos.le
    rw [h_scaled]
    exact h_lower_comparison
  have h_time_ns_upper :
      1000000000 * (travelTime UnitChoices.SI).val < (3.405 : ℝ) := by
    apply lt_of_mul_lt_mul_right _ hcoeff_pos.le
    rw [h_scaled]
    exact h_upper_comparison
  change
    |(travelTime nanosecondUnitChoices).val - 340 / 100| ≤
      (5 / 1000 : ℝ)
  rw [h_time_units, abs_le]
  constructor <;> norm_num <;> linarith

end

end ProblemPhyXMini0023
end PhyXMiniProblems
