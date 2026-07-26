import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0277

open Dimension

/-!
# Positive phase constant from an acceleration--time graph

The primary figure plots acceleration against time.  Its vertical axis is
labelled `a (m/s^2)`, its horizontal axis is labelled `t` without a printed
time unit, and the acceleration scale is `a_s = 4.0 m/s^2`.  Four equal grid
intervals separate zero from `a_s`.  At the plotted time origin the curve is
one grid interval above zero and is rising.  Thus the image supplies

`a(0) = a_s / 4 = 1 m/s^2`

together with a positive acceleration-graph slope at that instant.

The problem specifies the position convention

`x(t) = x_m cos (omega t + phi)`.

Lengths, times, angular frequencies, accelerations, and jerks below are
dimensionful Physlib quantities.  Real numbers are used only for coherent SI
readouts, the dimensionless phase measured in radians, grid counts, and the
displayed answer values.
-/

/-! ## Dimensionful oscillator quantities and SI readouts -/

/-- A signed one-dimensional displacement or displacement amplitude. -/
abbrev OscillatorLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time coordinate. -/
abbrev OscillatorTime : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- Angular frequency, with radians treated as dimensionless. -/
abbrev AngularFrequency : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A signed one-dimensional acceleration. -/
abbrev OscillatorAcceleration : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/--
A signed one-dimensional jerk, the physical slope of an acceleration--time
graph.
-/
abbrev OscillatorJerk : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical length in metres. -/
def metersValue (length : OscillatorLength) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical time in seconds. -/
def secondsValue (time : OscillatorTime) : ℝ :=
  (time UnitChoices.SI).val

/-- Read an angular frequency in radians per second. -/
def radiansPerSecondValue (frequency : AngularFrequency) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Read a signed acceleration in metres per second squared. -/
def metersPerSecondSquaredValue
    (acceleration : OscillatorAcceleration) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Read a signed jerk in metres per second cubed. -/
def metersPerSecondCubedValue (jerk : OscillatorJerk) : ℝ :=
  (jerk UnitChoices.SI).val

/-! ## Figure labels and harmonic-oscillator setup -/

/-- The two coordinate axes visible in the primary graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The physical quantity printed on each coordinate axis. -/
inductive AxisQuantity where
  | time_t
  | acceleration_a
  deriving DecidableEq, Repr

/--
Labels, units, scale, and grid data read from the primary figure.

The horizontal axis has no printed time unit.  The vertical label explicitly
uses metres and seconds squared; these units are represented by Physlib's
`LengthUnit` and `TimeUnit` rather than by an untyped string.
-/
structure AccelerationTimeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  horizontalAxisShowsUnit : Bool
  verticalAxisShowsUnit : Bool
  verticalLengthUnit : LengthUnit
  verticalTimeUnit : TimeUnit
  verticalDenominatorTimePower : ℕ
  verticalScaleAs : OscillatorAcceleration
  gridIntervalsFromZeroToAs : ℕ
  sinusoidalCurveVisible : Bool

/--
The physical quantities referred to by the question and acceleration graph.

The phase field stores the unknown requested by the problem, but no value is
assigned to it here.  Position, acceleration, and jerk are independent
dimensionful observables connected to the amplitude, angular frequency, and
phase only by the governing-law premise below.
-/
structure AccelerationGraphOscillator where
  graph : AccelerationTimeGraph
  positionAmplitudeXm : OscillatorLength
  angularFrequency : AngularFrequency
  phaseConstantRadians : ℝ
  position : OscillatorTime → OscillatorLength
  acceleration : OscillatorTime → OscillatorAcceleration
  jerk : OscillatorTime → OscillatorJerk
  accelerationAmplitude : OscillatorAcceleration
  plottedTimeOrigin : OscillatorTime

/-!
Primary-image evidence and the stated `a_s` calibration.  The curve meets the
marked extrema `a_s` and `-a_s`, so its acceleration amplitude equals the
scale.  At the vertical axis it is one of the four grid intervals above zero
and is rising.  The rising condition is recorded dimensionfully as positive
jerk, not as a premise about the phase.
-/
structure MatchesPrimaryAccelerationGraph
    (setup : AccelerationGraphOscillator) : Prop where
  horizontalAxisLabel :
    setup.graph.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.graph.axisQuantity .vertical = .acceleration_a
  horizontalUnitNotPrinted :
    setup.graph.horizontalAxisShowsUnit = false
  verticalUnitPrinted :
    setup.graph.verticalAxisShowsUnit = true
  verticalLengthUnitIsMeters :
    setup.graph.verticalLengthUnit = LengthUnit.meters
  verticalTimeUnitIsSeconds :
    setup.graph.verticalTimeUnit = TimeUnit.seconds
  verticalTimeUnitIsSquared :
    setup.graph.verticalDenominatorTimePower = 2
  sinusoidalCurveShown :
    setup.graph.sinusoidalCurveVisible = true
  scaleReadoutAs :
    metersPerSecondSquaredValue setup.graph.verticalScaleAs = 4
  fourGridIntervalsToScale :
    setup.graph.gridIntervalsFromZeroToAs = 4
  accelerationExtremaTouchScale :
    metersPerSecondSquaredValue setup.accelerationAmplitude =
      metersPerSecondSquaredValue setup.graph.verticalScaleAs
  plottedOriginReadout :
    secondsValue setup.plottedTimeOrigin = 0
  initialAccelerationOneGridAboveZero :
    metersPerSecondSquaredValue
        (setup.acceleration setup.plottedTimeOrigin) =
      metersPerSecondSquaredValue setup.graph.verticalScaleAs /
        (setup.graph.gridIntervalsFromZeroToAs : ℝ)
  curveRisingAtOrigin :
    0 < metersPerSecondCubedValue (setup.jerk setup.plottedTimeOrigin)

/-!
Nondegeneracy and the standard positive phase representative.  Restricting
the phase to one turn is a convention, not the requested numerical answer;
the graph ordinate and slope must still determine its quadrant and value.
-/
structure HasPhysicalHarmonicParameters
    (setup : AccelerationGraphOscillator) : Prop where
  positionAmplitudePositive :
    0 < metersValue setup.positionAmplitudeXm
  angularFrequencyPositive :
    0 < radiansPerSecondValue setup.angularFrequency
  accelerationAmplitudePositive :
    0 < metersPerSecondSquaredValue setup.accelerationAmplitude
  phasePositive :
    0 < setup.phaseConstantRadians
  phaseBelowFullTurn :
    setup.phaseConstantRadians < 2 * Real.pi

/-!
The governing simple-harmonic-motion laws in the plus-phase convention stated
in the question.  The acceleration equation is the second physical time
derivative of the position equation, and the jerk equation is its next time
derivative.  The last field relates the acceleration amplitude to
`x_m * omega^2`.

Physlib's `HarmonicOscillator.AmplitudePhase` instead uses scalar coordinates
and the convention `A cos (omega t - phi)`.  This local interface preserves
the problem's dimensionful observables and explicit plus-sign convention.
No field contains the solved phase, its cosine, or an answer choice.
-/
structure SatisfiesCosineHarmonicMotion
    (setup : AccelerationGraphOscillator) : Prop where
  harmonicPositionLaw :
    ∀ time : OscillatorTime,
      metersValue (setup.position time) =
        metersValue setup.positionAmplitudeXm *
          Real.cos
            (radiansPerSecondValue setup.angularFrequency *
                secondsValue time +
              setup.phaseConstantRadians)
  harmonicAccelerationLaw :
    ∀ time : OscillatorTime,
      metersPerSecondSquaredValue (setup.acceleration time) =
        -(metersValue setup.positionAmplitudeXm *
            radiansPerSecondValue setup.angularFrequency ^ 2) *
          Real.cos
            (radiansPerSecondValue setup.angularFrequency *
                secondsValue time +
              setup.phaseConstantRadians)
  harmonicJerkLaw :
    ∀ time : OscillatorTime,
      metersPerSecondCubedValue (setup.jerk time) =
        metersValue setup.positionAmplitudeXm *
          radiansPerSecondValue setup.angularFrequency ^ 3 *
          Real.sin
            (radiansPerSecondValue setup.angularFrequency *
                secondsValue time +
              setup.phaseConstantRadians)
  accelerationAmplitudeRelation :
    metersPerSecondSquaredValue setup.accelerationAmplitude =
      metersValue setup.positionAmplitudeXm *
        radiansPerSecondValue setup.angularFrequency ^ 2

/-! ## Displayed answers and target conclusions -/

/-- Labels of the four phase choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The phase in radians printed beside each answer label. -/
def AnswerChoice.radians : AnswerChoice → ℝ
  | .A => 148 / 100
  | .B => 165 / 100
  | .C => 224 / 100
  | .D => 182 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- Agreement with a phase displayed to the nearest hundredth of a radian. -/
def MatchesAnswerToNearestHundredth
    (phaseRadians : ℝ) (choice : AnswerChoice) : Prop :=
  |phaseRadians - choice.radians| < 1 / 200

/--
The initial acceleration readout and the acceleration-amplitude law give
`cos phi = -1/4`.
-/
lemma initial_phase_cosine_eq_neg_one_fourth
    (setup : AccelerationGraphOscillator)
    (hFigure : MatchesPrimaryAccelerationGraph setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesCosineHarmonicMotion setup) :
    Real.cos setup.phaseConstantRadians = -(1 : ℝ) / 4 := by
  have hAmplitude :
      metersPerSecondSquaredValue setup.accelerationAmplitude = 4 :=
    hFigure.accelerationExtremaTouchScale.trans hFigure.scaleReadoutAs
  have hInitial :
      metersPerSecondSquaredValue
          (setup.acceleration setup.plottedTimeOrigin) = 1 := by
    rw [hFigure.initialAccelerationOneGridAboveZero,
      hFigure.scaleReadoutAs, hFigure.fourGridIntervalsToScale]
    norm_num
  have hAccelerationLaw :=
    hLaws.harmonicAccelerationLaw setup.plottedTimeOrigin
  rw [hFigure.plottedOriginReadout] at hAccelerationLaw
  simp only [mul_zero, zero_add] at hAccelerationLaw
  rw [← hLaws.accelerationAmplitudeRelation, hAmplitude] at hAccelerationLaw
  linarith

/-!
The rising acceleration graph gives `sin phi > 0`.  Together with the
negative cosine and the positive one-turn convention, this puts the phase in
quadrant II.
-/
lemma phase_lies_in_second_quadrant
    (setup : AccelerationGraphOscillator)
    (hFigure : MatchesPrimaryAccelerationGraph setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesCosineHarmonicMotion setup) :
    setup.phaseConstantRadians ∈ Set.Ioo (Real.pi / 2) Real.pi := by
  have hJerkLaw := hLaws.harmonicJerkLaw setup.plottedTimeOrigin
  rw [hFigure.plottedOriginReadout] at hJerkLaw
  simp only [mul_zero, zero_add] at hJerkLaw
  have hJerkPos := hFigure.curveRisingAtOrigin
  rw [hJerkLaw] at hJerkPos
  have hCoefficientPos :
      0 < metersValue setup.positionAmplitudeXm *
        radiansPerSecondValue setup.angularFrequency ^ 3 :=
    mul_pos hPhysical.positionAmplitudePositive
      (pow_pos hPhysical.angularFrequencyPositive 3)
  have hSinPos : 0 < Real.sin setup.phaseConstantRadians := by
    rcases (mul_pos_iff.mp hJerkPos) with hPositive | hNegative
    · exact hPositive.2
    · exact (not_lt_of_ge hCoefficientPos.le hNegative.1).elim
  have hPhaseLtPi : setup.phaseConstantRadians < Real.pi := by
    by_contra hNotLt
    have hPiLe : Real.pi ≤ setup.phaseConstantRadians := le_of_not_gt hNotLt
    have hSinNonneg :
        0 ≤ Real.sin (setup.phaseConstantRadians - Real.pi) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hPiLe) (by
        linarith [hPhysical.phaseBelowFullTurn])
    rw [Real.sin_sub_pi] at hSinNonneg
    linarith
  have hCos :=
    initial_phase_cosine_eq_neg_one_fourth setup hFigure hPhysical hLaws
  have hHalfPiLt : Real.pi / 2 < setup.phaseConstantRadians := by
    by_contra hNotLt
    have hPhaseLe : setup.phaseConstantRadians ≤ Real.pi / 2 :=
      le_of_not_gt hNotLt
    have hCosNonneg : 0 ≤ Real.cos setup.phaseConstantRadians :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos, hPhysical.phasePositive]) hPhaseLe
    rw [hCos] at hCosNonneg
    norm_num at hCosNonneg
  constructor
  · exact hHalfPiLt
  · exact hPhaseLtPi

/-- On the selected quadrant, the exact phase is the principal inverse cosine. -/
lemma phase_constant_eq_arccos_neg_one_fourth
    (setup : AccelerationGraphOscillator)
    (hFigure : MatchesPrimaryAccelerationGraph setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesCosineHarmonicMotion setup) :
    setup.phaseConstantRadians = Real.arccos (-(1 : ℝ) / 4) := by
  rw [← initial_phase_cosine_eq_neg_one_fourth
    setup hFigure hPhysical hLaws]
  symm
  exact Real.arccos_cos hPhysical.phasePositive.le
    (phase_lies_in_second_quadrant setup hFigure hPhysical hLaws).2.le

/-- The exact inverse-cosine value rounds to `1.82 rad`, displayed as D. -/
lemma arccos_neg_one_fourth_matches_choice_D :
    MatchesAnswerToNearestHundredth
      (Real.arccos (-(1 : ℝ) / 4)) .D := by
  change |Real.arccos (-(1 : ℝ) / 4) - 182 / 100| < 1 / 200
  have hCosLower : -(1 : ℝ) / 4 < Real.cos (363 / 200 : ℝ) := by
    let y : ℝ := 363 / 1600
    have hyPos : 0 < y := by norm_num [y]
    have hyLtPi : y < Real.pi :=
      lt_of_lt_of_le (by norm_num [y]) Real.two_le_pi
    have hSinNonneg : 0 ≤ Real.sin y :=
      (Real.sin_pos_of_pos_of_lt_pi hyPos hyLtPi).le
    have hSinBound :=
      Real.sin_bound (x := y) (by
        norm_num [y, abs_of_nonneg hyPos.le])
    rw [abs_le] at hSinBound
    have hSinUpper : Real.sin y < (22507 : ℝ) / 100000 := by
      norm_num [y] at hSinBound ⊢
      linarith [hSinBound.2]
    have hSinSqUpper :
        Real.sin y ^ 2 < ((22507 : ℝ) / 100000) ^ 2 := by
      nlinarith
    have hCosQuarter :
        Real.cos ((363 / 200 : ℝ) / 4) =
          1 - 2 * Real.sin y ^ 2 := by
      rw [show (363 / 200 : ℝ) / 4 = 2 * y by norm_num [y],
        Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq y]
    have hCosQuarterLower :
        (8986 : ℝ) / 10000 <
          Real.cos ((363 / 200 : ℝ) / 4) := by
      rw [hCosQuarter]
      norm_num at hSinSqUpper ⊢
      linarith
    have hCosQuarterSqLower :
        ((8986 : ℝ) / 10000) ^ 2 <
          Real.cos ((363 / 200 : ℝ) / 4) ^ 2 := by
      nlinarith
    have hCosHalf :
        Real.cos ((363 / 200 : ℝ) / 2) =
          2 * Real.cos ((363 / 200 : ℝ) / 4) ^ 2 - 1 := by
      rw [show (363 / 200 : ℝ) / 2 =
          2 * ((363 / 200 : ℝ) / 4) by ring,
        Real.cos_two_mul]
    have hCosHalfLower :
        (6149 : ℝ) / 10000 <
          Real.cos ((363 / 200 : ℝ) / 2) := by
      rw [hCosHalf]
      norm_num at hCosQuarterSqLower ⊢
      linarith
    have hCosHalfSqLower :
        ((6149 : ℝ) / 10000) ^ 2 <
          Real.cos ((363 / 200 : ℝ) / 2) ^ 2 := by
      nlinarith
    rw [show (363 / 200 : ℝ) =
        2 * ((363 / 200 : ℝ) / 2) by ring,
      Real.cos_two_mul]
    norm_num at hCosHalfSqLower ⊢
    linarith
  have hCosUpper : Real.cos (73 / 40 : ℝ) < -(1 : ℝ) / 4 := by
    let y : ℝ := 73 / 320
    have hyPos : 0 < y := by norm_num [y]
    have hyLtPi : y < Real.pi :=
      lt_of_lt_of_le (by norm_num [y]) Real.two_le_pi
    have hSinNonneg : 0 ≤ Real.sin y :=
      (Real.sin_pos_of_pos_of_lt_pi hyPos hyLtPi).le
    have hSinBound :=
      Real.sin_bound (x := y) (by
        norm_num [y, abs_of_nonneg hyPos.le])
    rw [abs_le] at hSinBound
    have hSinLower : (226 : ℝ) / 1000 < Real.sin y := by
      norm_num [y] at hSinBound ⊢
      linarith [hSinBound.1]
    have hSinSqLower :
        ((226 : ℝ) / 1000) ^ 2 < Real.sin y ^ 2 := by
      nlinarith
    have hCosQuarter :
        Real.cos ((73 / 40 : ℝ) / 4) =
          1 - 2 * Real.sin y ^ 2 := by
      rw [show (73 / 40 : ℝ) / 4 = 2 * y by norm_num [y],
        Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq y]
    have hCosQuarterUpper :
        Real.cos ((73 / 40 : ℝ) / 4) <
          (89785 : ℝ) / 100000 := by
      rw [hCosQuarter]
      norm_num at hSinSqLower ⊢
      linarith
    have hCosQuarterPos :
        0 < Real.cos ((73 / 40 : ℝ) / 4) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.one_le_pi_div_two]
    have hCosQuarterSqUpper :
        Real.cos ((73 / 40 : ℝ) / 4) ^ 2 <
          ((89785 : ℝ) / 100000) ^ 2 := by
      nlinarith
    have hCosHalf :
        Real.cos ((73 / 40 : ℝ) / 2) =
          2 * Real.cos ((73 / 40 : ℝ) / 4) ^ 2 - 1 := by
      rw [show (73 / 40 : ℝ) / 2 =
          2 * ((73 / 40 : ℝ) / 4) by ring,
        Real.cos_two_mul]
    have hCosHalfUpper :
        Real.cos ((73 / 40 : ℝ) / 2) <
          (6123 : ℝ) / 10000 := by
      rw [hCosHalf]
      norm_num at hCosQuarterSqUpper ⊢
      linarith
    have hCosHalfPos :
        0 < Real.cos ((73 / 40 : ℝ) / 2) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.one_le_pi_div_two]
    have hCosHalfSqUpper :
        Real.cos ((73 / 40 : ℝ) / 2) ^ 2 <
          ((6123 : ℝ) / 10000) ^ 2 := by
      nlinarith
    rw [show (73 / 40 : ℝ) =
        2 * ((73 / 40 : ℝ) / 2) by ring,
      Real.cos_two_mul]
    norm_num at hCosHalfSqUpper ⊢
    linarith
  have hLower :
      (363 : ℝ) / 200 < Real.arccos (-(1 : ℝ) / 4) := by
    have h := Real.arccos_lt_arccos (x := -(1 : ℝ) / 4)
      (y := Real.cos (363 / 200 : ℝ)) (by norm_num) hCosLower
      (Real.cos_le_one _)
    rw [Real.arccos_cos (by norm_num)
      (by nlinarith [Real.two_le_pi])] at h
    exact h
  have hUpper :
      Real.arccos (-(1 : ℝ) / 4) < (73 : ℝ) / 40 := by
    have h := Real.arccos_lt_arccos
      (x := Real.cos (73 / 40 : ℝ)) (y := -(1 : ℝ) / 4)
      (Real.neg_one_le_cos _) hCosUpper (by norm_num)
    rw [Real.arccos_cos (by norm_num)
      (by nlinarith [Real.two_le_pi])] at h
    exact h
  rw [abs_lt]
  constructor <;> norm_num at * <;> linarith

/-!
At `t = 0`, the graph gives `a/a_s = 1/4` and positive slope.  Since

`a(t) = -a_s cos (omega t + phi)`,

the phase has cosine `-1/4` and lies in quadrant II.  Therefore

`phi = arccos (-1/4) approximately 1.82348 rad`.

It rounds to `1.82 rad`, choice D, and is at least as close to D as to every
other displayed choice.  The formal target deliberately uses a rounding
predicate rather than the false exact equality `phi = 1.82`.

This formalizes `thm:physics:phyx_mini_0277:target`.
-/
theorem problem_phyx_mini_0277
    (setup : AccelerationGraphOscillator)
    (hFigure : MatchesPrimaryAccelerationGraph setup)
    (hPhysical : HasPhysicalHarmonicParameters setup)
    (hLaws : SatisfiesCosineHarmonicMotion setup) :
    Real.cos setup.phaseConstantRadians = -(1 : ℝ) / 4 ∧
      setup.phaseConstantRadians = Real.arccos (-(1 : ℝ) / 4) ∧
      MatchesAnswerToNearestHundredth
        setup.phaseConstantRadians recordedAnswerChoice ∧
      ∀ choice : AnswerChoice,
        |setup.phaseConstantRadians - recordedAnswerChoice.radians| ≤
          |setup.phaseConstantRadians - choice.radians| := by
  have hCos :=
    initial_phase_cosine_eq_neg_one_fourth setup hFigure hPhysical hLaws
  have hPhase :=
    phase_constant_eq_arccos_neg_one_fourth setup hFigure hPhysical hLaws
  refine ⟨hCos, hPhase, ?_, ?_⟩
  · rw [hPhase]
    simpa [recordedAnswerChoice] using
      arccos_neg_one_fourth_matches_choice_D
  · intro choice
    rw [hPhase]
    have hRound := arccos_neg_one_fourth_matches_choice_D
    change |Real.arccos (-(1 : ℝ) / 4) - 182 / 100| <
      1 / 200 at hRound
    have hRoundLe := hRound.le
    rw [abs_lt] at hRound
    cases choice with
    | A =>
        change |Real.arccos (-(1 : ℝ) / 4) - 182 / 100| ≤
          |Real.arccos (-(1 : ℝ) / 4) - 148 / 100|
        calc
          |Real.arccos (-(1 : ℝ) / 4) - 182 / 100| ≤
              1 / 200 := hRoundLe
          _ ≤ Real.arccos (-(1 : ℝ) / 4) - 148 / 100 := by
            linarith [hRound.1]
          _ ≤ |Real.arccos (-(1 : ℝ) / 4) - 148 / 100| :=
            le_abs_self _
    | B =>
        change |Real.arccos (-(1 : ℝ) / 4) - 182 / 100| ≤
          |Real.arccos (-(1 : ℝ) / 4) - 165 / 100|
        calc
          |Real.arccos (-(1 : ℝ) / 4) - 182 / 100| ≤
              1 / 200 := hRoundLe
          _ ≤ Real.arccos (-(1 : ℝ) / 4) - 165 / 100 := by
            linarith [hRound.1]
          _ ≤ |Real.arccos (-(1 : ℝ) / 4) - 165 / 100| :=
            le_abs_self _
    | C =>
        change |Real.arccos (-(1 : ℝ) / 4) - 182 / 100| ≤
          |Real.arccos (-(1 : ℝ) / 4) - 224 / 100|
        calc
          |Real.arccos (-(1 : ℝ) / 4) - 182 / 100| ≤
              1 / 200 := hRoundLe
          _ ≤ -(Real.arccos (-(1 : ℝ) / 4) - 224 / 100) := by
            linarith [hRound.2]
          _ ≤ |Real.arccos (-(1 : ℝ) / 4) - 224 / 100| :=
            neg_le_abs _
    | D => exact le_rfl

end PhyXMiniProblems.ProblemPhyXMini0277
