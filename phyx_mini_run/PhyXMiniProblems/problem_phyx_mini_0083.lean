import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Slit width from an `α` versus `sin θ` graph

This file models the single-slit diffraction experiment in problem
`phyx_mini_0083`. The wavelength and slit width are unit-aware physical
lengths. The graph coordinates are scalar readouts: `sin θ` is dimensionless,
and `α` is the dimensionless diffraction phase parameter reported in radians.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0083

/-- A signed physical length represented independently of a chosen unit system. -/
abbrev DimLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- Read a physical length as a real scalar in the specified length unit. -/
def lengthValueIn (unit : LengthUnit) (length : DimLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The metre readout used in the dimensionless single-slit phase law. -/
def metersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.meters length

/-- The nanometre readout used for the stated wavelength. -/
def nanometersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- The micrometre readout used by the four answer choices. -/
def micrometersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.micrometers length

/--
The monochromatic illumination and single slit. The wavelength is the stated
`610 nm`; the slit width is the physical quantity requested by the problem.
-/
structure SingleSlitExperiment where
  /-- Vacuum wavelength `λ` of the incident monochromatic light. -/
  lightWavelength : DimLength
  /-- Width `a` of the single slit. -/
  slitWidth : DimLength

/--
The plotted graph. Its horizontal coordinate is a scalar value of `sin θ`, and
its vertical coordinate is the phase parameter `α` read in radians. The field
`alphaScaleRadians` is the figure label `αₛ` at the top of the vertical axis.
-/
structure AlphaVersusSineThetaGraph where
  /-- Vertical graph readout `α` for a supplied horizontal readout `sin θ`. -/
  alphaRadiansAtSine : ℝ → ℝ
  /-- The vertical-axis scale label `αₛ`, in radians. -/
  alphaScaleRadians : ℝ

/--
The Fraunhofer single-slit phase-parameter law

`α = (π a / λ) sin θ`

on the displayed interval `0 ≤ sin θ ≤ 1`. Metre readouts are used for both
lengths, so their quotient is dimensionless. This governing law contains no
numerical value for the requested slit width.
-/
def SatisfiesSingleSlitPhaseLaw
    (experiment : SingleSlitExperiment)
    (graph : AlphaVersusSineThetaGraph) : Prop :=
  0 < metersValue experiment.lightWavelength ∧
    0 < metersValue experiment.slitWidth ∧
    ∀ sineTheta : ℝ,
      0 ≤ sineTheta → sineTheta ≤ 1 →
        graph.alphaRadiansAtSine sineTheta =
          Real.pi * metersValue experiment.slitWidth /
              metersValue experiment.lightWavelength * sineTheta

/--
The problem-text and primary-figure readouts: `λ = 610 nm`, `αₛ = 12 rad`,
and the bold line from `(0, 0)` to `(1, αₛ)`. The universal equation records
the displayed straight line throughout the horizontal range. No slit-width
readout occurs in this predicate.
-/
def HasStatedWavelengthAndGraphReadouts
    (experiment : SingleSlitExperiment)
    (graph : AlphaVersusSineThetaGraph) : Prop :=
  nanometersValue experiment.lightWavelength = 610 ∧
    graph.alphaScaleRadians = 12 ∧
    graph.alphaRadiansAtSine 0 = 0 ∧
    graph.alphaRadiansAtSine 1 = graph.alphaScaleRadians ∧
    ∀ sineTheta : ℝ,
      0 ≤ sineTheta → sineTheta ≤ 1 →
        graph.alphaRadiansAtSine sineTheta =
          graph.alphaScaleRadians * sineTheta

/-- Labels of the four multiple-choice answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/--
Each displayed slit-width choice, in hundredths of a micrometre. Thus the
recorded value for choice C is `233 / 100 μm = 2.33 μm`.
-/
def answerSlitWidthHundredthsMicrometers : AnswerChoice → ℤ
  | .A => 210
  | .B => 250
  | .C => 233
  | .D => 195

/--
The slit width inferred from the stated wavelength and graph rounds to
`2.33 μm`, the dataset's recorded answer choice C.

This formalizes `thm:physics:phyx_mini_0083:target`.
-/
theorem slitWidth_rounds_to_recordedAnswerC
    (experiment : SingleSlitExperiment)
    (graph : AlphaVersusSineThetaGraph)
    (h_readouts : HasStatedWavelengthAndGraphReadouts experiment graph)
    (h_phase : SatisfiesSingleSlitPhaseLaw experiment graph) :
    round (100 * micrometersValue experiment.slitWidth) =
      answerSlitWidthHundredthsMicrometers .C := by
  rcases h_readouts with
    ⟨h_wavelength_nm, h_alpha_scale, _, h_graph_endpoint, _⟩
  rcases h_phase with ⟨h_wavelength_pos, _, h_phase_law⟩
  have h_wavelength_units :
      nanometersValue experiment.lightWavelength =
        1000000000 * metersValue experiment.lightWavelength := by
    have h := congrArg WithDim.val <| experiment.lightWavelength.property
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices)
    norm_num [nanometersValue, metersValue, lengthValueIn,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.toReal] at h ⊢
    exact h
  have h_slit_units :
      micrometersValue experiment.slitWidth =
        1000000 * metersValue experiment.slitWidth := by
    have h := congrArg WithDim.val <| experiment.slitWidth.property
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.micrometers } : UnitChoices)
    norm_num [micrometersValue, metersValue, lengthValueIn,
      UnitChoices.dimScale, LengthUnit.micrometers, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.toReal] at h ⊢
    exact h
  have h_wavelength_m :
      metersValue experiment.lightWavelength = (61 / 100000000 : ℝ) := by
    nlinarith
  have h_graph_one : graph.alphaRadiansAtSine 1 = 12 :=
    h_graph_endpoint.trans h_alpha_scale
  have h_phase_one := h_phase_law 1 (by norm_num) (by norm_num)
  rw [h_graph_one] at h_phase_one
  norm_num at h_phase_one
  have h_phase_mul :
      12 * metersValue experiment.lightWavelength =
        Real.pi * metersValue experiment.slitWidth :=
    (eq_div_iff (ne_of_gt h_wavelength_pos)).mp h_phase_one
  have h_scaled_width :
      Real.pi * (100 * micrometersValue experiment.slitWidth) = 732 := by
    calc
      Real.pi * (100 * micrometersValue experiment.slitWidth) =
          Real.pi * (100 * (1000000 * metersValue experiment.slitWidth)) := by
            rw [h_slit_units]
      _ = 100000000 * (Real.pi * metersValue experiment.slitWidth) := by ring
      _ = 100000000 * (12 * metersValue experiment.lightWavelength) := by
        rw [← h_phase_mul]
      _ = 732 := by rw [h_wavelength_m]; norm_num
  have h_width_exact :
      100 * micrometersValue experiment.slitWidth = 732 / Real.pi :=
    (eq_div_iff Real.pi_ne_zero).2 (by simpa [mul_comm] using h_scaled_width)
  change round (100 * micrometersValue experiment.slitWidth) = (233 : ℤ)
  rw [h_width_exact]
  have hkeep : True := trivial
  clear * - hkeep
  clear hkeep
  -- The present imports expose the exact half-angle value at `π / 32` and
  -- a certified sine approximation.  Together they give the modest decimal
  -- bounds on `π` needed for the final hundredth-micrometre rounding.
  have hr2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hr2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2_lower : (1.4142 : ℝ) < Real.sqrt 2 := by
    nlinarith
  have hr2_upper : Real.sqrt 2 < (1.4143 : ℝ) := by
    nlinarith
  have hr3_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
  have hr3_sq : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt hr3_arg
  have hr3_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hr3_lower : (1.8477 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith
  have hr3_upper : Real.sqrt (2 + Real.sqrt 2) < (1.8478 : ℝ) := by
    nlinarith
  have hr4_arg : 0 ≤ (2 : ℝ) + Real.sqrt (2 + Real.sqrt 2) := by positivity
  have hr4_sq : (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
      2 + Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt hr4_arg
  have hr4_nonneg :
      0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := Real.sqrt_nonneg _
  have hr4_lower :
      (1.96155 : ℝ) < Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith
  have hr4_upper :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) < (1.96158 : ℝ) := by
    nlinarith
  have hs_arg :
      0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith
  have hs_sq :
      (Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sq_sqrt hs_arg
  have hs_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) :=
    Real.sqrt_nonneg _
  have hs_lower :
      (0.196 : ℝ) <
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) := by
    nlinarith
  have hs_upper :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) <
        (0.1961 : ℝ) := by
    nlinarith
  have hsin_lower : (0.098 : ℝ) < Real.sin (Real.pi / 32) := by
    rw [Real.sin_pi_div_thirty_two]
    linarith
  have hsin_upper : Real.sin (Real.pi / 32) < (0.09805 : ℝ) := by
    rw [Real.sin_pi_div_thirty_two]
    linarith
  have hx_nonneg : 0 ≤ Real.pi / 32 := by positivity
  have hx_le_eighth : Real.pi / 32 ≤ (1 / 8 : ℝ) := by
    nlinarith [Real.pi_le_four]
  have hx_abs : |Real.pi / 32| ≤ 1 := by
    rw [abs_of_nonneg hx_nonneg]
    linarith
  have hsin_approx := Real.sin_bound hx_abs
  have hsin_approx_lower := (abs_le.mp hsin_approx).1
  have hsin_approx_upper := (abs_le.mp hsin_approx).2
  have hx_cube_nonneg : 0 ≤ (Real.pi / 32) ^ 3 := by positivity
  have hx_cube_le : (Real.pi / 32) ^ 3 ≤ (1 / 8 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx_nonneg hx_le_eighth 3
  have hx_fourth_le : (Real.pi / 32) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx_nonneg hx_le_eighth 4
  have hpi_lower : (3.135 : ℝ) < Real.pi := by
    by_contra h
    have hpi_le : Real.pi ≤ (3.135 : ℝ) := le_of_not_gt h
    rw [abs_of_nonneg hx_nonneg] at hsin_approx_upper
    nlinarith
  have hpi_lt_coarse : Real.pi < (3.2 : ℝ) := by
    by_contra h
    have hpi_ge : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
    rw [abs_of_nonneg hx_nonneg] at hsin_approx_lower
    nlinarith
  have hx_le_tenth : Real.pi / 32 ≤ (1 / 10 : ℝ) := by
    linarith
  have hx_cube_le_tenth : (Real.pi / 32) ^ 3 ≤ (1 / 10 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx_nonneg hx_le_tenth 3
  have hx_fourth_le_tenth : (Real.pi / 32) ^ 4 ≤ (1 / 10 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hx_nonneg hx_le_tenth 4
  have hpi_upper : Real.pi < (3.148 : ℝ) := by
    by_contra h
    have hpi_ge : (3.148 : ℝ) ≤ Real.pi := le_of_not_gt h
    rw [abs_of_nonneg hx_nonneg] at hsin_approx_lower
    nlinarith
  rw [round_eq_iff]
  constructor
  · apply (le_div_iff₀ Real.pi_pos).2
    nlinarith only [hpi_upper]
  · apply (div_lt_iff₀ Real.pi_pos).2
    nlinarith only [hpi_lower]

end PhyXMiniProblems.ProblemPhyXMini0083
