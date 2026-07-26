import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0082

open Dimension

/-!
# Intensities of the first two fringes of a finite double slit

Monochromatic light of wavelength `440 nm` illuminates two equal finite-width
slits. The supplied graph plots irradiance (called intensity in the problem)
in `mW/cm²` against angular position in degrees. Its central peak is
`7 mW/cm²`, and the diffraction envelope calibrates the slit separation as
four slit widths.

Lengths and irradiances below are dimensionful Physlib quantities. Real
numbers occur only as readouts in the units printed in the source. Angular
position uses Mathlib's `Real.Angle` type.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/--
A nonnegative physical irradiance. Power per area has dimension
`mass / time³`, since the two powers of length in power and area cancel.
-/
abbrev IrradianceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- The numerical readout of a physical length in nanometers. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.nanometers}).val : ℝ)

/--
The numerical irradiance readout in `mW/cm²`. An SI irradiance readout is in
`W/m²`, and `1 mW/cm² = 10 W/m²`.
-/
def irradianceInMilliwattsPerSquareCentimeter
    (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ) / 10

/-- Convert the numerical degree markings on the horizontal axis to an angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- The two labeled axes in the supplied plot. -/
inductive FigureAxis where
  | angularPosition
  | irradiance
  deriving DecidableEq, Repr

/-- Units printed beside the two graph axes. -/
inductive FigureAxisUnit where
  | degrees
  | milliwattsPerSquareCentimeter
  deriving DecidableEq, Repr

/-- Color of the measured diffraction trace in the source image. -/
inductive TraceColor where
  | green
  deriving DecidableEq, Repr

/-- Metadata explicitly visible on the intensity-versus-angle graph. -/
structure DiffractionGraph where
  horizontalAxis : FigureAxis
  verticalAxis : FigureAxis
  horizontalUnit : FigureAxisUnit
  verticalUnit : FigureAxisUnit
  traceColor : TraceColor
  hasGrid : Bool
  traceShownThroughDegrees : ℝ

/--
All named physical quantities in the finite-width double-slit experiment.
The slit width and separation remain dimensionful quantities. The functions
`angularIrradiance` and `fringeAngle` represent the physical curve and the
angular location of each interference fringe.
-/
structure DoubleSlitSetup where
  wavelength : LengthQuantity
  slitWidth : LengthQuantity
  slitSeparation : LengthQuantity
  centralIrradiance : IrradianceQuantity
  angularIrradiance : Real.Angle → IrradianceQuantity
  fringeAngle : ℕ → Real.Angle
  graph : DiffractionGraph

/-- Positive wavelength, slit dimensions, and central irradiance. -/
def HasPhysicalParameters (setup : DoubleSlitSetup) : Prop :=
  0 < lengthInNanometers setup.wavelength ∧
    0 < lengthInNanometers setup.slitWidth ∧
    0 < lengthInNanometers setup.slitSeparation ∧
    0 < irradianceInMilliwattsPerSquareCentimeter setup.centralIrradiance

/-!
Problem and figure readouts. The graph supplies a `7 mW/cm²` central peak,
uses degrees and `mW/cm²` on its axes, and shows a green trace through about
`10°`. The fourth constructive fringe coincides with the first diffraction
minimum, calibrating the separation as four slit widths. No requested
noncentral fringe intensity or answer-choice value occurs in this predicate.
-/
def MatchesProblemAndFigure (setup : DoubleSlitSetup) : Prop :=
  lengthInNanometers setup.wavelength = 440 ∧
    irradianceInMilliwattsPerSquareCentimeter setup.centralIrradiance = 7 ∧
    lengthInNanometers setup.slitSeparation =
      4 * lengthInNanometers setup.slitWidth ∧
    setup.fringeAngle 0 = degrees 0 ∧
    setup.graph.horizontalAxis = .angularPosition ∧
    setup.graph.verticalAxis = .irradiance ∧
    setup.graph.horizontalUnit = .degrees ∧
    setup.graph.verticalUnit = .milliwattsPerSquareCentimeter ∧
    setup.graph.traceColor = .green ∧
    setup.graph.hasGrid = true ∧
    setup.graph.traceShownThroughDegrees = 10

/-!
The governing Fraunhofer law for two equal rectangular slits. The first
factor is the single-slit diffraction envelope and the second is the
two-source interference factor. `Real.sinc x = sin x / x` away from zero and
has the continuous value `1` at zero.

The second field is the constructive-interference condition
`d sin θₘ / λ = m`. Both relations hold for arbitrary angles or fringe orders
and contain neither of the requested numerical intensities.
-/
structure SatisfiesFraunhoferDoubleSlitLaw
    (setup : DoubleSlitSetup) : Prop where
  angularIntensityLaw : ∀ angle : Real.Angle,
    irradianceInMilliwattsPerSquareCentimeter
        (setup.angularIrradiance angle) =
      irradianceInMilliwattsPerSquareCentimeter setup.centralIrradiance *
        (Real.sinc
          (Real.pi *
            (lengthInNanometers setup.slitWidth /
              lengthInNanometers setup.wavelength) *
            Real.Angle.sin angle)) ^ 2 *
        (Real.cos
          (Real.pi *
            (lengthInNanometers setup.slitSeparation /
              lengthInNanometers setup.wavelength) *
            Real.Angle.sin angle)) ^ 2
  constructiveInterference : ∀ order : ℕ,
    (lengthInNanometers setup.slitSeparation /
        lengthInNanometers setup.wavelength) *
      Real.Angle.sin (setup.fringeAngle order) = order

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The intensity value in `mW/cm²` printed beside each answer label. -/
def answerIntensity : AnswerChoice → ℝ
  | .A => 6.4
  | .B => 5.2
  | .C => 5.7
  | .D => 4.8

/-- Agreement with a graph-displayed intensity to within `0.1 mW/cm²`. -/
def AgreesWithDisplayedIntensity (actual displayed : ℝ) : Prop :=
  |actual - displayed| ≤ 0.1

/-- The answer choices refer to the first noncentral (`m = 1`) fringe. -/
def MatchesFirstFringeAnswer
    (setup : DoubleSlitSetup) (choice : AnswerChoice) : Prop :=
  AgreesWithDisplayedIntensity
    (irradianceInMilliwattsPerSquareCentimeter
      (setup.angularIrradiance (setup.fringeAngle 1)))
    (answerIntensity choice)

/--
At every constructive fringe, the figure calibration reduces the diffraction
envelope phase to `mπ/4` and the interference factor to `cos²(mπ)`.
-/
lemma irradiance_at_constructive_fringe
    (setup : DoubleSlitSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_law : SatisfiesFraunhoferDoubleSlitLaw setup)
    (order : ℕ) :
    irradianceInMilliwattsPerSquareCentimeter
        (setup.angularIrradiance (setup.fringeAngle order)) =
      7 * (Real.sinc (Real.pi * order / 4)) ^ 2 *
        (Real.cos (Real.pi * order)) ^ 2 := by
  have h_wavelength_ne :
      lengthInNanometers setup.wavelength ≠ 0 :=
    ne_of_gt h_physical.1
  have h_central :
      irradianceInMilliwattsPerSquareCentimeter setup.centralIrradiance = 7 :=
    h_figure.2.1
  have h_separation :
      lengthInNanometers setup.slitSeparation =
        4 * lengthInNanometers setup.slitWidth :=
    h_figure.2.2.1
  have h_constructive := h_law.constructiveInterference order
  have h_envelope :
      (lengthInNanometers setup.slitWidth /
          lengthInNanometers setup.wavelength) *
          Real.Angle.sin (setup.fringeAngle order) =
        (order : ℝ) / 4 := by
    calc
      (lengthInNanometers setup.slitWidth /
            lengthInNanometers setup.wavelength) *
            Real.Angle.sin (setup.fringeAngle order) =
          ((4 * lengthInNanometers setup.slitWidth) /
              lengthInNanometers setup.wavelength *
              Real.Angle.sin (setup.fringeAngle order)) / 4 := by
            field_simp [h_wavelength_ne]
      _ = (order : ℝ) / 4 := by
        rw [← h_separation, h_constructive]
  have h_envelope_phase :
      Real.pi *
          (lengthInNanometers setup.slitWidth /
            lengthInNanometers setup.wavelength) *
          Real.Angle.sin (setup.fringeAngle order) =
        Real.pi * order / 4 := by
    calc
      Real.pi *
            (lengthInNanometers setup.slitWidth /
              lengthInNanometers setup.wavelength) *
            Real.Angle.sin (setup.fringeAngle order) =
          Real.pi *
            ((lengthInNanometers setup.slitWidth /
                lengthInNanometers setup.wavelength) *
              Real.Angle.sin (setup.fringeAngle order)) := by ring
      _ = Real.pi * order / 4 := by rw [h_envelope]; ring
  have h_interference_phase :
      Real.pi *
          (lengthInNanometers setup.slitSeparation /
            lengthInNanometers setup.wavelength) *
          Real.Angle.sin (setup.fringeAngle order) =
        Real.pi * order := by
    calc
      Real.pi *
            (lengthInNanometers setup.slitSeparation /
              lengthInNanometers setup.wavelength) *
            Real.Angle.sin (setup.fringeAngle order) =
          Real.pi *
            ((lengthInNanometers setup.slitSeparation /
                lengthInNanometers setup.wavelength) *
              Real.Angle.sin (setup.fringeAngle order)) := by ring
      _ = Real.pi * order := by rw [h_constructive]
  rw [h_law.angularIntensityLaw, h_central, h_envelope_phase,
    h_interference_phase]

/-- Exact values predicted for the first two noncentral fringe peaks. -/
lemma first_two_fringe_intensities_exact
    (setup : DoubleSlitSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_law : SatisfiesFraunhoferDoubleSlitLaw setup) :
    irradianceInMilliwattsPerSquareCentimeter
        (setup.angularIrradiance (setup.fringeAngle 1)) =
        56 / Real.pi ^ 2 ∧
      irradianceInMilliwattsPerSquareCentimeter
        (setup.angularIrradiance (setup.fringeAngle 2)) =
        28 / Real.pi ^ 2 := by
  constructor
  · rw [irradiance_at_constructive_fringe setup h_physical h_figure h_law 1]
    norm_num only [Nat.cast_one, mul_one]
    rw [Real.sinc_of_ne_zero
        (div_ne_zero Real.pi_ne_zero (by norm_num)),
      Real.sin_pi_div_four, Real.cos_pi]
    have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    field_simp [Real.pi_ne_zero]
    nlinarith
  · rw [irradiance_at_constructive_fringe setup h_physical h_figure h_law 2]
    have harg : Real.pi * (2 : ℕ) / 4 = Real.pi / 2 := by
      norm_num only [Nat.cast_ofNat]
      ring
    have hcos : Real.cos (Real.pi * (2 : ℕ)) = 1 := by
      norm_num only [Nat.cast_ofNat]
      rw [show Real.pi * 2 = 2 * Real.pi by ring, Real.cos_two_pi]
    rw [harg, Real.sinc_of_ne_zero
        (div_ne_zero Real.pi_ne_zero (by norm_num)),
      Real.sin_pi_div_two, hcos]
    field_simp [Real.pi_ne_zero]
    ring

/-- The exact predictions agree with the graph's displayed peak heights. -/
lemma exact_fringe_values_agree_with_display :
    AgreesWithDisplayedIntensity (56 / Real.pi ^ 2) 5.7 ∧
      AgreesWithDisplayedIntensity (28 / Real.pi ^ 2) 2.9 := by
  have hsqrt_two_sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_two_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_two_lower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hsqrt_two_sq, hsqrt_two_nonneg]
  have hsqrt_two_upper : Real.sqrt 2 < (283 / 200 : ℝ) := by
    nlinarith only [hsqrt_two_sq, hsqrt_two_nonneg]
  have hsqrt_two_plus_sq :
      Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hsqrt_two_plus_nonneg : 0 ≤ Real.sqrt (2 + Real.sqrt 2) :=
    Real.sqrt_nonneg _
  have hsqrt_two_plus_lower :
      (184753 / 100000 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hsqrt_two_plus_sq, hsqrt_two_plus_nonneg,
      hsqrt_two_lower]
  have hsqrt_two_plus_upper :
      Real.sqrt (2 + Real.sqrt 2) < (1849 / 1000 : ℝ) := by
    nlinarith only [hsqrt_two_plus_sq, hsqrt_two_plus_nonneg,
      hsqrt_two_upper]
  have hsin_sixteen_radicand :
      0 ≤ 2 - Real.sqrt (2 + Real.sqrt 2) := by
    linarith only [hsqrt_two_plus_upper]
  have hsin_sixteen_sqrt_sq :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt hsin_sixteen_radicand
  have hsin_sixteen_sqrt_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have hsin_sixteen_lower :
      (777 / 4000 : ℝ) < Real.sin (Real.pi / 16) := by
    rw [Real.sin_pi_div_sixteen]
    nlinarith only [hsin_sixteen_sqrt_sq, hsin_sixteen_sqrt_nonneg,
      hsqrt_two_plus_upper]
  have hsin_sixteen_lt_pi :
      Real.sin (Real.pi / 16) < Real.pi / 16 :=
    Real.sin_lt (by positivity)
  have hpi_lower : (777 / 250 : ℝ) < Real.pi := by
    linarith only [hsin_sixteen_lower, hsin_sixteen_lt_pi]
  have hpi_lower_product :
      0 < (Real.pi - 777 / 250) * (Real.pi + 777 / 250) := by
    positivity
  have hpi_sq_lower : (280 / 29 : ℝ) < Real.pi ^ 2 := by
    nlinarith only [hpi_lower_product]
  have hsqrt_three_levels_sq :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) ^ 2 =
        2 + Real.sqrt (2 + Real.sqrt 2) :=
    Real.sq_sqrt (by positivity)
  have hsqrt_three_levels_nonneg :
      0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sqrt_nonneg _
  have hsqrt_three_levels_lower :
      (196151 / 100000 : ℝ) <
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    nlinarith only [hsqrt_three_levels_sq, hsqrt_three_levels_nonneg,
      hsqrt_two_plus_lower]
  have hsqrt_three_levels_upper :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) < 2 := by
    nlinarith only [hsqrt_three_levels_sq, hsqrt_three_levels_nonneg,
      hsqrt_two_plus_upper]
  have hsin_thirty_two_radicand :
      0 ≤ 2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    linarith only [hsqrt_three_levels_upper]
  have hsin_thirty_two_sqrt_sq :
      Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
        2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sq_sqrt hsin_thirty_two_radicand
  have hsin_thirty_two_sqrt_nonneg :
      0 ≤ Real.sqrt (2 - Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) :=
    Real.sqrt_nonneg _
  have hsin_thirty_two_upper :
      Real.sin (Real.pi / 32) < (981 / 10000 : ℝ) := by
    rw [Real.sin_pi_div_thirty_two]
    nlinarith only [hsin_thirty_two_sqrt_sq,
      hsin_thirty_two_sqrt_nonneg, hsqrt_three_levels_lower]
  have hcos_thirty_two_sqrt_sq :
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) ^ 2 =
        2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) :=
    Real.sq_sqrt (by positivity)
  have hcos_thirty_two_sqrt_nonneg :
      0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2))) :=
    Real.sqrt_nonneg _
  have hcos_thirty_two_lower :
      (993 / 1000 : ℝ) < Real.cos (Real.pi / 32) := by
    rw [Real.cos_pi_div_thirty_two]
    nlinarith only [hcos_thirty_two_sqrt_sq,
      hcos_thirty_two_sqrt_nonneg, hsqrt_three_levels_lower]
  have htan_thirty_two_upper :
      Real.tan (Real.pi / 32) < (1581 / 16000 : ℝ) := by
    rw [Real.tan_eq_sin_div_cos]
    rw [div_lt_iff₀ (by positivity : 0 < Real.cos (Real.pi / 32))]
    nlinarith only [hsin_thirty_two_upper, hcos_thirty_two_lower]
  have hpi_div_thirty_two_lt_tan :
      Real.pi / 32 < Real.tan (Real.pi / 32) :=
    Real.lt_tan (by positivity) (by nlinarith only [Real.pi_pos])
  have hpi_upper : Real.pi < (1581 / 500 : ℝ) := by
    linarith only [hpi_div_thirty_two_lt_tan, htan_thirty_two_upper]
  have hpi_upper_product :
      0 < (1581 / 500 - Real.pi) * (1581 / 500 + Real.pi) := by
    positivity
  have hpi_sq_upper : Real.pi ^ 2 < 10 := by
    nlinarith only [hpi_upper_product]
  have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hfirst_lower : (28 / 5 : ℝ) ≤ 56 / Real.pi ^ 2 := by
    rw [le_div_iff₀ hpi_sq_pos]
    nlinarith only [hpi_sq_upper]
  have hfirst_upper : 56 / Real.pi ^ 2 ≤ (29 / 5 : ℝ) := by
    rw [div_le_iff₀ hpi_sq_pos]
    nlinarith only [hpi_sq_lower]
  have hsecond_lower : (14 / 5 : ℝ) ≤ 28 / Real.pi ^ 2 := by
    rw [le_div_iff₀ hpi_sq_pos]
    nlinarith only [hpi_sq_upper]
  have hsecond_upper : 28 / Real.pi ^ 2 ≤ (3 : ℝ) := by
    rw [div_le_iff₀ hpi_sq_pos]
    nlinarith only [hpi_sq_lower]
  constructor
  · rw [AgreesWithDisplayedIntensity, abs_le]
    constructor <;> norm_num <;>
      linarith only [hfirst_lower, hfirst_upper]
  · rw [AgreesWithDisplayedIntensity, abs_le]
    constructor <;> norm_num <;>
      linarith only [hsecond_lower, hsecond_upper]

/-!
The finite-width double-slit law predicts `56/π² ≈ 5.7 mW/cm²` for the
`m = 1` fringe and `28/π² ≈ 2.9 mW/cm²` for the `m = 2` fringe. Thus the
first displayed fringe selects answer C.

This formalizes `thm:physics:phyx_mini_0082:target`.
-/
theorem problem_phyx_mini_0082
    (setup : DoubleSlitSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_law : SatisfiesFraunhoferDoubleSlitLaw setup) :
    irradianceInMilliwattsPerSquareCentimeter
        (setup.angularIrradiance (setup.fringeAngle 1)) =
        56 / Real.pi ^ 2 ∧
      irradianceInMilliwattsPerSquareCentimeter
        (setup.angularIrradiance (setup.fringeAngle 2)) =
        28 / Real.pi ^ 2 ∧
      AgreesWithDisplayedIntensity
        (irradianceInMilliwattsPerSquareCentimeter
          (setup.angularIrradiance (setup.fringeAngle 1))) 5.7 ∧
      AgreesWithDisplayedIntensity
        (irradianceInMilliwattsPerSquareCentimeter
          (setup.angularIrradiance (setup.fringeAngle 2))) 2.9 ∧
      MatchesFirstFringeAnswer setup .C := by
  rcases first_two_fringe_intensities_exact setup h_physical h_figure h_law with
    ⟨h_first, h_second⟩
  rcases exact_fringe_values_agree_with_display with
    ⟨h_first_display, h_second_display⟩
  have h_first_agrees :
      AgreesWithDisplayedIntensity
        (irradianceInMilliwattsPerSquareCentimeter
          (setup.angularIrradiance (setup.fringeAngle 1))) 5.7 := by
    rw [h_first]
    exact h_first_display
  have h_second_agrees :
      AgreesWithDisplayedIntensity
        (irradianceInMilliwattsPerSquareCentimeter
          (setup.angularIrradiance (setup.fringeAngle 2))) 2.9 := by
    rw [h_second]
    exact h_second_display
  refine ⟨h_first, h_second, h_first_agrees, h_second_agrees, ?_⟩
  simpa [MatchesFirstFringeAnswer, answerIntensity] using h_first_agrees

end PhyXMiniProblems.ProblemPhyXMini0082
