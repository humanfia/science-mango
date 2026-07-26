import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0094

open Dimension

/-!
# Two ideal polarizers with an adjustable relative angle

A linearly polarized beam of original irradiance `I₀` first reaches an ideal
polarizer aligned with the beam's polarization.  It then reaches a second
ideal polarizer whose axis makes the figure angle `φ` with the first axis.
The detector point `P` is beyond the second polarizer, and its requested
irradiance is `I₀ / 10`.

Irradiance is represented by a Physlib dimensionful quantity.  Its physical
dimension is mass divided by time cubed, equivalently power per area.  Real
numbers below are used only for radian angles, dimensionless transmission
factors, and explicitly named SI or degree readouts.
-/

/-- A nonnegative physical optical irradiance (power per area). -/
abbrev IrradianceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- The numerical irradiance readout in SI units, watts per square meter. -/
def irradianceInWattsPerSquareMeter (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ)

/-- A beam together with its physical irradiance and polarization direction. -/
structure LinearlyPolarizedLight where
  irradianceI0 : IrradianceQuantity
  polarizationAxisRadians : ℝ

/-- An ideal linear polarizer, specified by its axis direction in radians. -/
structure IdealLinearPolarizer where
  axisRadians : ℝ

/--
The quantities and figure labels in the two-polarizer setup.  The reference
direction for axis angles is the vertical axis of the first polarizer in the
figure.  `relativeAnglePhiRadians` is the displayed `φ`, and `irradianceAtP`
is the physical irradiance at the displayed point `P`.
-/
structure TwoPolarizerSetup where
  incomingLight : LinearlyPolarizedLight
  firstPolarizer : IdealLinearPolarizer
  secondPolarizer : IdealLinearPolarizer
  irradianceAfterFirst : IrradianceQuantity
  irradianceAtP : IrradianceQuantity
  relativeAnglePhiRadians : ℝ

/-- Convert a radian angle readout to degrees. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/--
The source statement and figure geometry: the incident polarization is aligned
with the first polarizer, the first axis is the vertical reference, and `φ` is
the directed rotation from the first polarizer to the second.
-/
def MatchesProblemAndFigure (setup : TwoPolarizerSetup) : Prop :=
  setup.incomingLight.polarizationAxisRadians =
      setup.firstPolarizer.axisRadians ∧
    setup.firstPolarizer.axisRadians = 0 ∧
    setup.secondPolarizer.axisRadians - setup.firstPolarizer.axisRadians =
      setup.relativeAnglePhiRadians

/-- Positive incident light and the acute angle branch depicted in the figure. -/
def HasPhysicalParameters (setup : TwoPolarizerSetup) : Prop :=
  0 < irradianceInWattsPerSquareMeter setup.incomingLight.irradianceI0 ∧
    setup.relativeAnglePhiRadians ∈ Set.Icc 0 (Real.pi / 2)

/-!
Malus's law for an ideal polarizer.  The output irradiance equals the input
irradiance multiplied by the dimensionless factor `cos² θ`, where `θ` is the
angle between the incident polarization and the polarizer axis.
-/
def ObeysMalusLaw
    (inputIrradiance outputIrradiance : IrradianceQuantity)
    (relativeAngleRadians : ℝ) : Prop :=
  irradianceInWattsPerSquareMeter outputIrradiance =
    irradianceInWattsPerSquareMeter inputIrradiance *
      Real.cos relativeAngleRadians ^ 2

/-!
The two governing ideal-polarizer laws.  After the first polarizer the outgoing
polarization is along its axis, so that axis is the incident direction for the
second application of Malus's law.  No requested value of `φ` occurs here.
-/
structure SatisfiesIdealPolarizerLaws (setup : TwoPolarizerSetup) : Prop where
  firstPolarizer : ObeysMalusLaw
    setup.incomingLight.irradianceI0
    setup.irradianceAfterFirst
    (setup.firstPolarizer.axisRadians -
      setup.incomingLight.polarizationAxisRadians)
  secondPolarizer : ObeysMalusLaw
    setup.irradianceAfterFirst
    setup.irradianceAtP
    (setup.secondPolarizer.axisRadians -
      setup.firstPolarizer.axisRadians)

/-!
The experimental adjustment condition from the question: point `P` is to
receive one tenth of the original irradiance.  This is input data for solving
for `φ`, not an assumption about the requested angle.
-/
def HasRequestedIrradianceAtP (setup : TwoPolarizerSetup) : Prop :=
  irradianceInWattsPerSquareMeter setup.irradianceAtP =
    irradianceInWattsPerSquareMeter setup.incomingLight.irradianceI0 / 10

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The degree value displayed beside each answer choice. -/
def answerAngleDegrees : AnswerChoice → ℝ
  | .A => 71.6
  | .B => 72.3
  | .C => 71.9
  | .D => 72.2

/-- Agreement with a displayed angle to the nearest tenth of a degree. -/
def MatchesAnswerToNearestTenth
    (angleRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |radiansToDegrees angleRadians - answerAngleDegrees choice| ≤ 0.05

/-- Alignment makes the first ideal polarizer transmit the full irradiance. -/
lemma aligned_first_polarizer_preserves_irradiance
    (setup : TwoPolarizerSetup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_laws : SatisfiesIdealPolarizerLaws setup) :
    irradianceInWattsPerSquareMeter setup.irradianceAfterFirst =
      irradianceInWattsPerSquareMeter setup.incomingLight.irradianceI0 := by
  rcases h_figure with ⟨haligned, _hfirstAxis, _hrelative⟩
  have hfirst := h_laws.firstPolarizer
  unfold ObeysMalusLaw at hfirst
  rw [haligned, sub_self, Real.cos_zero] at hfirst
  norm_num at hfirst ⊢
  exact hfirst

/-- The requested detector readout reduces Malus's law to `cos² φ = 1/10`. -/
lemma malus_equation_for_relative_angle
    (setup : TwoPolarizerSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_laws : SatisfiesIdealPolarizerLaws setup)
    (h_pointP : HasRequestedIrradianceAtP setup) :
    Real.cos setup.relativeAnglePhiRadians ^ 2 = (1 : ℝ) / 10 := by
  have hfirst :=
    aligned_first_polarizer_preserves_irradiance setup h_figure h_laws
  have hsecond := h_laws.secondPolarizer
  unfold ObeysMalusLaw at hsecond
  rw [h_figure.2.2, hfirst] at hsecond
  unfold HasRequestedIrradianceAtP at h_pointP
  nlinarith only [hsecond, h_pointP, h_physical.1]

/-- The acute exact solution rounds to the degree value printed for choice A. -/
lemma acute_exact_angle_matches_choice_A :
    MatchesAnswerToNearestTenth
      (Real.arccos (Real.sqrt ((1 : ℝ) / 10))) .A := by
  set_option maxHeartbeats 800000 in
    let s : ℝ := Real.sqrt ((1 : ℝ) / 10)
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      positivity
    have hs_sq : s ^ 2 = (1 : ℝ) / 10 := by
      dsimp [s]
      exact Real.sq_sqrt (by norm_num)
    have hs_lower : (0.31622 : ℝ) ≤ s := by
      nlinarith only [hs_nonneg, hs_sq]
    have hs_upper : s ≤ (0.31623 : ℝ) := by
      nlinarith only [hs_nonneg, hs_sq]

    -- We first obtain the modest numerical bounds on `π` needed below from
    -- the exact value of `sin (π / 16)` and `Real.sin_bound`.
    have hr2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hr2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hr2_lower : (1.41421 : ℝ) < Real.sqrt 2 := by
      nlinarith only [hr2_sq, hr2_nonneg]
    have hr2_upper : Real.sqrt 2 < (1.414214 : ℝ) := by
      nlinarith only [hr2_sq, hr2_nonneg]
    have hr3_arg : 0 ≤ (2 : ℝ) + Real.sqrt 2 := by positivity
    have hr3_sq :
        Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
      Real.sq_sqrt hr3_arg
    have hr3_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
      Real.sqrt_nonneg _
    have hr3_lower :
        (1.8477581 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
      nlinarith only [hr2_lower, hr3_sq, hr3_nonneg]
    have hr3_upper :
        Real.sqrt (2 + Real.sqrt 2) < (1.8477595 : ℝ) := by
      nlinarith only [hr2_upper, hr3_sq, hr3_nonneg]
    have hsixteen_arg :
        0 ≤ (2 : ℝ) - Real.sqrt (2 + Real.sqrt 2) := by
      linarith only [hr3_upper]
    have hsixteen_sq :
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
          2 - Real.sqrt (2 + Real.sqrt 2) :=
      Real.sq_sqrt hsixteen_arg
    have hsixteen_nonneg :
        0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
      Real.sqrt_nonneg _
    have hsixteen_lower :
        (0.39018 : ℝ) <
          Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) := by
      nlinarith only [hr3_upper, hsixteen_sq, hsixteen_nonneg]
    have hsixteen_upper :
        Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) <
          (0.390182 : ℝ) := by
      nlinarith only [hr3_lower, hsixteen_sq, hsixteen_nonneg]
    have hsin_pi_sixteen_lower :
        (0.19509 : ℝ) < Real.sin (Real.pi / 16) := by
      rw [Real.sin_pi_div_sixteen]
      linarith only [hsixteen_lower]
    have hsin_pi_sixteen_upper :
        Real.sin (Real.pi / 16) < (0.195091 : ℝ) := by
      rw [Real.sin_pi_div_sixteen]
      linarith only [hsixteen_upper]
    let x : ℝ := Real.pi / 16
    have hx_nonneg : 0 ≤ x := by positivity
    have hx_le_quarter : x ≤ (1 / 4 : ℝ) := by
      dsimp [x]
      nlinarith only [Real.pi_le_four]
    have hx_abs : |x| ≤ 1 := by
      rw [abs_of_nonneg hx_nonneg]
      linarith only [hx_le_quarter]
    have hsin_x_bound := Real.sin_bound hx_abs
    rw [abs_of_nonneg hx_nonneg] at hsin_x_bound
    have hsin_x_lower := (abs_le.mp hsin_x_bound).1
    have hsin_x_upper := (abs_le.mp hsin_x_bound).2
    have hpi_gt_31 : (3.1 : ℝ) < Real.pi := by
      by_contra h
      have hpi_le : Real.pi ≤ (3.1 : ℝ) := le_of_not_gt h
      have hx_le : x ≤ (3.1 : ℝ) / 16 := by
        dsimp [x]
        nlinarith only [hpi_le]
      have hxfourth : x ^ 4 ≤ ((3.1 : ℝ) / 16) ^ 4 :=
        pow_le_pow_left₀ hx_nonneg hx_le 4
      dsimp [x] at hsin_x_upper hxfourth
      nlinarith only [hsin_pi_sixteen_lower, hsin_x_upper, hxfourth,
        hpi_le, sq_nonneg (Real.pi / 16)]
    have hpi_gt_3139 : (3.139 : ℝ) < Real.pi := by
      have hx_lower : (3.1 : ℝ) / 16 ≤ x := by
        dsimp [x]
        nlinarith only [hpi_gt_31.le]
      have hxcube : ((3.1 : ℝ) / 16) ^ 3 ≤ x ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hx_lower 3
      by_contra h
      have hpi_le : Real.pi ≤ (3.139 : ℝ) := le_of_not_gt h
      have hx_le : x ≤ (3.139 : ℝ) / 16 := by
        dsimp [x]
        nlinarith only [hpi_le]
      have hxfourth : x ^ 4 ≤ ((3.139 : ℝ) / 16) ^ 4 :=
        pow_le_pow_left₀ hx_nonneg hx_le 4
      dsimp [x] at hsin_x_upper hxcube hxfourth
      nlinarith only [hsin_pi_sixteen_lower, hsin_x_upper, hxcube,
        hxfourth, hpi_le]
    have hpi_lower : (3.14 : ℝ) < Real.pi := by
      have hx_lower : (3.139 : ℝ) / 16 ≤ x := by
        dsimp [x]
        nlinarith only [hpi_gt_3139.le]
      have hxcube : ((3.139 : ℝ) / 16) ^ 3 ≤ x ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hx_lower 3
      by_contra h
      have hpi_le : Real.pi ≤ (3.14 : ℝ) := le_of_not_gt h
      have hx_le : x ≤ (3.14 : ℝ) / 16 := by
        dsimp [x]
        nlinarith only [hpi_le]
      have hxfourth : x ^ 4 ≤ ((3.14 : ℝ) / 16) ^ 4 :=
        pow_le_pow_left₀ hx_nonneg hx_le 4
      dsimp [x] at hsin_x_upper hxcube hxfourth
      nlinarith only [hsin_pi_sixteen_lower, hsin_x_upper, hxcube,
        hxfourth, hpi_le]
    have hpi_upper : Real.pi < (3.2 : ℝ) := by
      have hxcube : x ^ 3 ≤ (1 / 4 : ℝ) ^ 3 :=
        pow_le_pow_left₀ hx_nonneg hx_le_quarter 3
      have hxfourth : x ^ 4 ≤ (1 / 4 : ℝ) ^ 4 :=
        pow_le_pow_left₀ hx_nonneg hx_le_quarter 4
      by_contra h
      have hpi_ge : (3.2 : ℝ) ≤ Real.pi := le_of_not_gt h
      dsimp [x] at hsin_x_lower hxcube hxfourth
      nlinarith only [hsin_pi_sixteen_upper, hsin_x_lower, hxcube,
        hxfourth, hpi_ge]

    -- The exact sine at 18 degrees anchors both endpoint estimates.
    have hr5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    have hr5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hr5_lower : (2.236 : ℝ) ≤ Real.sqrt 5 := by
      nlinarith only [hr5_nonneg, hr5_sq]
    have hr5_upper : Real.sqrt 5 ≤ (2.2361 : ℝ) := by
      nlinarith only [hr5_nonneg, hr5_sq]
    have hsin_pi_ten :
        Real.sin (Real.pi / 10) = (Real.sqrt 5 - 1) / 4 := by
      rw [← Real.cos_pi_div_two_sub]
      rw [show Real.pi / 2 - Real.pi / 10 =
          2 * (Real.pi / 5) by ring]
      rw [Real.cos_two_mul, Real.cos_pi_div_five]
      nlinarith only [hr5_sq]
    have hsin_pi_ten_nonneg : 0 ≤ Real.sin (Real.pi / 10) := by
      rw [hsin_pi_ten]
      linarith only [hr5_lower]
    have hsin_pi_ten_lower :
        (0.309 : ℝ) ≤ Real.sin (Real.pi / 10) := by
      rw [hsin_pi_ten]
      linarith only [hr5_lower]
    have hsin_pi_ten_upper :
        Real.sin (Real.pi / 10) ≤ (0.309025 : ℝ) := by
      rw [hsin_pi_ten]
      linarith only [hr5_upper]
    have hcos_pi_ten_nonneg : 0 ≤ Real.cos (Real.pi / 10) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> nlinarith only [Real.pi_pos]
    have htrig_pi_ten := Real.sin_sq_add_cos_sq (Real.pi / 10)
    have hsin_pi_ten_sq_upper :
        Real.sin (Real.pi / 10) ^ 2 ≤ (0.309025 : ℝ) ^ 2 := by
      nlinarith only [hsin_pi_ten_nonneg, hsin_pi_ten_upper]
    have hcos_pi_ten_lower :
        (0.95 : ℝ) ≤ Real.cos (Real.pi / 10) := by
      nlinarith only [hcos_pi_ten_nonneg, htrig_pi_ten,
        hsin_pi_ten_sq_upper]

    -- 71.55 degrees has complementary angle 18.45 degrees.
    let dLower : ℝ := Real.pi / 400
    have hdLower_nonneg : 0 ≤ dLower := by positivity
    have hdLower_lower : (0.00785 : ℝ) < dLower := by
      dsimp [dLower]
      nlinarith only [hpi_lower]
    have hdLower_upper : dLower ≤ (0.01 : ℝ) := by
      dsimp [dLower]
      nlinarith only [Real.pi_le_four]
    have hdLower_abs : |dLower| ≤ 1 := by
      rw [abs_of_nonneg hdLower_nonneg]
      linarith only [hdLower_upper]
    have hsin_dLower_bound := Real.sin_bound hdLower_abs
    have hcos_dLower_bound := Real.cos_bound hdLower_abs
    rw [abs_le, abs_of_nonneg hdLower_nonneg] at hsin_dLower_bound
    rw [abs_le, abs_of_nonneg hdLower_nonneg] at hcos_dLower_bound
    have hdLower_sq : dLower ^ 2 ≤ (0.01 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hdLower_nonneg hdLower_upper 2
    have hdLower_cube : dLower ^ 3 ≤ (0.01 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hdLower_nonneg hdLower_upper 3
    have hdLower_fourth : dLower ^ 4 ≤ (0.01 : ℝ) ^ 4 :=
      pow_le_pow_left₀ hdLower_nonneg hdLower_upper 4
    have hsin_dLower_lower :
        (0.007849 : ℝ) ≤ Real.sin dLower := by
      nlinarith only [hdLower_lower, hdLower_cube, hdLower_fourth,
        hsin_dLower_bound.1]
    have hcos_dLower_lower :
        (0.99994 : ℝ) ≤ Real.cos dLower := by
      nlinarith only [hdLower_sq, hdLower_fourth, hcos_dLower_bound.1]
    have hfirstLowerProduct :
        (0.309 : ℝ) * 0.99994 ≤
          Real.sin (Real.pi / 10) * Real.cos dLower :=
      mul_le_mul hsin_pi_ten_lower hcos_dLower_lower
        (by norm_num) hsin_pi_ten_nonneg
    have hsecondLowerProduct :
        (0.95 : ℝ) * 0.007849 ≤
          Real.cos (Real.pi / 10) * Real.sin dLower :=
      mul_le_mul hcos_pi_ten_lower hsin_dLower_lower
        (by norm_num) hcos_pi_ten_nonneg
    have hsin_lower_complement :
        (0.31623 : ℝ) ≤ Real.sin (41 * Real.pi / 400) := by
      rw [show 41 * Real.pi / 400 =
          Real.pi / 10 + dLower by dsimp [dLower]; ring, Real.sin_add]
      nlinarith only [hfirstLowerProduct, hsecondLowerProduct]

    -- 71.65 degrees has complementary angle 18.35 degrees.
    let dUpper : ℝ := 7 * Real.pi / 3600
    have hdUpper_nonneg : 0 ≤ dUpper := by positivity
    have hdUpper_upper : dUpper < (0.006223 : ℝ) := by
      dsimp [dUpper]
      nlinarith only [hpi_upper]
    have hdUpper_abs : |dUpper| ≤ 1 := by
      rw [abs_of_nonneg hdUpper_nonneg]
      linarith only [hdUpper_upper]
    have hsin_dUpper_bound := Real.sin_bound hdUpper_abs
    rw [abs_le, abs_of_nonneg hdUpper_nonneg] at hsin_dUpper_bound
    have hdUpper_fourth : dUpper ^ 4 ≤ (0.007 : ℝ) ^ 4 := by
      apply pow_le_pow_left₀ hdUpper_nonneg _ 4
      linarith only [hdUpper_upper]
    have hdUpper_cube_nonneg : 0 ≤ dUpper ^ 3 := by positivity
    have hsin_dUpper_upper :
        Real.sin dUpper ≤ (0.006224 : ℝ) := by
      nlinarith only [hdUpper_upper, hdUpper_cube_nonneg,
        hdUpper_fourth, hsin_dUpper_bound.2]
    have hsin_dUpper_nonneg : 0 ≤ Real.sin dUpper :=
      Real.sin_nonneg_of_nonneg_of_le_pi hdUpper_nonneg
        (by dsimp [dUpper]; nlinarith only [Real.pi_pos])
    have hfirstUpperProduct :
        Real.sin (Real.pi / 10) * Real.cos dUpper ≤ (0.309025 : ℝ) := by
      calc
        Real.sin (Real.pi / 10) * Real.cos dUpper ≤
            Real.sin (Real.pi / 10) * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_le_one dUpper)
            hsin_pi_ten_nonneg
        _ ≤ (0.309025 : ℝ) := by
          simpa using hsin_pi_ten_upper
    have hsecondUpperProduct :
        Real.cos (Real.pi / 10) * Real.sin dUpper ≤ (0.006224 : ℝ) := by
      have := mul_le_mul (Real.cos_le_one (Real.pi / 10))
        hsin_dUpper_upper hsin_dUpper_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      norm_num at this ⊢
      exact this
    have hsin_upper_complement :
        Real.sin (367 * Real.pi / 3600) ≤ (0.31622 : ℝ) := by
      rw [show 367 * Real.pi / 3600 =
          Real.pi / 10 + dUpper by dsimp [dUpper]; ring, Real.sin_add]
      nlinarith only [hfirstUpperProduct, hsecondUpperProduct]

    have hcos_lower_endpoint :
        s ≤ Real.cos (159 * Real.pi / 400) := by
      rw [show 159 * Real.pi / 400 =
          Real.pi / 2 - 41 * Real.pi / 400 by ring,
        Real.cos_pi_div_two_sub]
      exact hs_upper.trans hsin_lower_complement
    have hcos_upper_endpoint :
        Real.cos (1433 * Real.pi / 3600) ≤ s := by
      rw [show 1433 * Real.pi / 3600 =
          Real.pi / 2 - 367 * Real.pi / 3600 by ring,
        Real.cos_pi_div_two_sub]
      exact hsin_upper_complement.trans hs_lower
    have hlower_nonneg : 0 ≤ 159 * Real.pi / 400 := by positivity
    have hlower_le_pi : 159 * Real.pi / 400 ≤ Real.pi := by
      nlinarith only [Real.pi_pos]
    have hupper_nonneg : 0 ≤ 1433 * Real.pi / 3600 := by positivity
    have hupper_le_pi : 1433 * Real.pi / 3600 ≤ Real.pi := by
      nlinarith only [Real.pi_pos]
    have hlower_angle :
        159 * Real.pi / 400 ≤ Real.arccos s := by
      have h :=
        Real.arccos_le_arccos hcos_lower_endpoint
      rw [Real.arccos_cos hlower_nonneg hlower_le_pi] at h
      exact h
    have hupper_angle :
        Real.arccos s ≤ 1433 * Real.pi / 3600 := by
      have h :=
        Real.arccos_le_arccos hcos_upper_endpoint
      rw [Real.arccos_cos hupper_nonneg hupper_le_pi] at h
      exact h

    change
      |radiansToDegrees (Real.arccos s) - answerAngleDegrees .A| ≤ 0.05
    simp only [radiansToDegrees, answerAngleDegrees]
    rw [abs_le]
    constructor
    · have hcleared :
          (71.55 : ℝ) * Real.pi ≤ Real.arccos s * 180 := by
        nlinarith only [hlower_angle]
      have hdegrees :=
        (le_div_iff₀ Real.pi_pos).2 hcleared
      nlinarith only [hdegrees]
    · have hcleared :
          Real.arccos s * 180 ≤ (71.65 : ℝ) * Real.pi := by
        nlinarith only [hupper_angle]
      have hdegrees :=
        (div_le_iff₀ Real.pi_pos).2 hcleared
      nlinarith only [hdegrees]

/-!
On the acute branch shown in the figure, `cos² φ = 1/10` has the unique
solution `φ = arccos (sqrt (1/10))`.  In degrees this is approximately
`71.565°`, so the one-decimal answer is `71.6°`, choice A.

This formalizes `thm:physics:phyx_mini_0094:target`.
-/
theorem problem_phyx_mini_0094
    (setup : TwoPolarizerSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_laws : SatisfiesIdealPolarizerLaws setup)
    (h_pointP : HasRequestedIrradianceAtP setup) :
    Real.cos setup.relativeAnglePhiRadians ^ 2 = (1 : ℝ) / 10 ∧
      setup.relativeAnglePhiRadians =
        Real.arccos (Real.sqrt ((1 : ℝ) / 10)) ∧
      MatchesAnswerToNearestTenth setup.relativeAnglePhiRadians .A := by
  have hmalus :=
    malus_equation_for_relative_angle setup h_physical h_figure h_laws h_pointP
  have hphi_nonneg : 0 ≤ setup.relativeAnglePhiRadians :=
    h_physical.2.1
  have hphi_le_half_pi :
      setup.relativeAnglePhiRadians ≤ Real.pi / 2 :=
    h_physical.2.2
  have hcos_nonneg : 0 ≤ Real.cos setup.relativeAnglePhiRadians := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith only [hphi_nonneg, Real.pi_pos]
    · exact hphi_le_half_pi
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((1 : ℝ) / 10) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      Real.sqrt ((1 : ℝ) / 10) ^ 2 = (1 : ℝ) / 10 :=
    Real.sq_sqrt (by norm_num)
  have hcos :
      Real.cos setup.relativeAnglePhiRadians =
        Real.sqrt ((1 : ℝ) / 10) := by
    nlinarith only [hmalus, hsqrt_sq, hcos_nonneg, hsqrt_nonneg]
  have hphi_le_pi : setup.relativeAnglePhiRadians ≤ Real.pi := by
    nlinarith only [hphi_le_half_pi, Real.pi_pos]
  have hangle :
      setup.relativeAnglePhiRadians =
        Real.arccos (Real.sqrt ((1 : ℝ) / 10)) := by
    have harccos_cos :=
      Real.arccos_cos hphi_nonneg hphi_le_pi
    rw [hcos] at harccos_cos
    exact harccos_cos.symm
  refine ⟨hmalus, hangle, ?_⟩
  rw [hangle]
  exact acute_exact_angle_matches_choice_A

end PhyXMiniProblems.ProblemPhyXMini0094
