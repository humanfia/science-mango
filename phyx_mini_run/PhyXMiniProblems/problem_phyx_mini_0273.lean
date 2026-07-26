import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

/-!
# Radial acceleration corresponding to a simple harmonic motion graph

The supplied figure plots the signed spring-block displacement `x` against
time `t`.  Its primary-image readouts are a `7 cm` amplitude and successive
crests at `t = 0` and at the marked time `t_s = 40 ms`; the intermediate
trough is at `20 ms`.  Thus `t_s` is one period.  (The auxiliary prose says
`8 cm`, but the curve itself is one grid division below the `8 cm` tick, and
the recorded answer is consistent with `7 cm`.)

Physical lengths, durations, inverse-time angular frequencies, and
accelerations are represented by Physlib's unit-independent dimensionful
quantities.  Real numbers below are only readouts in explicitly selected
units or dimensionless radian arguments.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0273

open Dimension

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical length, used for amplitudes and circle radii. -/
abbrev LengthMagnitudeQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length, used for the one-dimensional position `x(t)`. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyMagnitudeQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative acceleration magnitude, with dimension length per time squared. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative length in a selected length unit. -/
def lengthMagnitudeReadout
    (unit : LengthUnit) (quantity : LengthMagnitudeQuantity) : ℝ :=
  ((quantity {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed displacement in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (quantity : SignedLengthQuantity) : ℝ :=
  (quantity {UnitChoices.SI with length := unit}).val

/-- Read a duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (quantity : TimeQuantity) : ℝ :=
  ((quantity {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read an angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (quantity : AngularFrequencyMagnitudeQuantity) : ℝ :=
  ((quantity {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read an acceleration magnitude in coherent selected length and time units. -/
def accelerationMagnitudeReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (quantity : AccelerationMagnitudeQuantity) : ℝ :=
  ((quantity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a nonnegative length. -/
def lengthInMeters (quantity : LengthMagnitudeQuantity) : ℝ :=
  lengthMagnitudeReadout LengthUnit.meters quantity

/-- Second readout of a duration. -/
def timeInSeconds (quantity : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds quantity

/-- SI radian-per-second readout of an angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (quantity : AngularFrequencyMagnitudeQuantity) : ℝ :=
  angularFrequencyReadout TimeUnit.seconds quantity

/-- SI meter-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (quantity : AccelerationMagnitudeQuantity) : ℝ :=
  accelerationMagnitudeReadout LengthUnit.meters TimeUnit.seconds quantity

/-! ## Primary-figure vocabulary and physical setup -/

/-- Variables printed beside the two graph axes. -/
inductive GraphAxisVariable where
  | time_t
  | displacement_x
  deriving DecidableEq, Repr

/-- Unit abbreviations printed beside the two graph axes. -/
inductive GraphAxisUnit where
  | milliseconds
  | centimeters
  deriving DecidableEq, Repr

/-- The special time symbol printed below the second crest. -/
inductive MarkedTimeLabel where
  | t_s
  deriving DecidableEq, Repr

/-- The oscillator described in the problem statement. -/
inductive OscillatorKind where
  | blockOnSpring
  deriving DecidableEq, Repr

/-- The auxiliary motion whose projection corresponds to the SHM. -/
inductive CircularMotionKind where
  | uniform
  deriving DecidableEq, Repr

/-!
The dimensionful data and qualitative labels present in the supplied graph.
The position function is independent data; it is not defined as a cosine or
as an answer formula.
-/
structure PositionTimeGraph where
  position_x : TimeQuantity → SignedLengthQuantity
  amplitude : LengthMagnitudeQuantity
  timeOrigin : TimeQuantity
  troughTime : TimeQuantity
  markedTime_ts : TimeQuantity
  period : TimeQuantity
  horizontalAxisVariable : GraphAxisVariable
  verticalAxisVariable : GraphAxisVariable
  horizontalAxisUnit : GraphAxisUnit
  verticalAxisUnit : GraphAxisUnit
  markedTimeLabel : MarkedTimeLabel
  showsSinusoidalTrace : Bool
  showsGrid : Bool

/-!
The spring-block SHM and the corresponding uniform circular motion.  The two
angular frequencies, the circle radius, and the radial acceleration are kept
as independent physical quantities until related by the governing laws below.
-/
structure SHMCircularMotionSetup where
  graph : PositionTimeGraph
  oscillatorKind : OscillatorKind
  shmAngularFrequency : AngularFrequencyMagnitudeQuantity
  circleKind : CircularMotionKind
  circleRadius : LengthMagnitudeQuantity
  circleAngularSpeed : AngularFrequencyMagnitudeQuantity
  radialAccelerationMagnitude : AccelerationMagnitudeQuantity

/-!
Problem-text and primary-image evidence.  In the image the `8 cm` and `-8 cm`
numbers label grid lines; the curve reaches only `7 cm` and `-7 cm`.  The
crest--trough--crest times establish a `40 ms` crest-to-crest period.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : SHMCircularMotionSetup) : Prop where
  blockOnSpring : setup.oscillatorKind = .blockOnSpring
  uniformCircularMotion : setup.circleKind = .uniform
  timeAxisVariable : setup.graph.horizontalAxisVariable = .time_t
  displacementAxisVariable :
    setup.graph.verticalAxisVariable = .displacement_x
  timeAxisMilliseconds :
    setup.graph.horizontalAxisUnit = .milliseconds
  displacementAxisCentimeters :
    setup.graph.verticalAxisUnit = .centimeters
  markedTimeIs_ts : setup.graph.markedTimeLabel = .t_s
  sinusoidalTraceShown : setup.graph.showsSinusoidalTrace = true
  gridShown : setup.graph.showsGrid = true
  originTimeMilliseconds :
    timeReadout TimeUnit.milliseconds setup.graph.timeOrigin = 0
  originCrestCentimeters :
    signedLengthReadout LengthUnit.centimeters
        (setup.graph.position_x setup.graph.timeOrigin) = 7
  troughTimeMilliseconds :
    timeReadout TimeUnit.milliseconds setup.graph.troughTime = 20
  troughDisplacementCentimeters :
    signedLengthReadout LengthUnit.centimeters
        (setup.graph.position_x setup.graph.troughTime) = -7
  markedTimeMilliseconds :
    timeReadout TimeUnit.milliseconds setup.graph.markedTime_ts = 40
  markedTimeCrestCentimeters :
    signedLengthReadout LengthUnit.centimeters
        (setup.graph.position_x setup.graph.markedTime_ts) = 7
  amplitudeCentimeters :
    lengthMagnitudeReadout LengthUnit.centimeters setup.graph.amplitude = 7
  crestToCrestPeriod : setup.graph.period = setup.graph.markedTime_ts

/-- Positivity and nondegeneracy conditions for the depicted motions. -/
structure HasPhysicalParameters (setup : SHMCircularMotionSetup) : Prop where
  amplitudePositive :
    ∀ lengthUnit,
      0 < lengthMagnitudeReadout lengthUnit setup.graph.amplitude
  periodPositive :
    ∀ timeUnit, 0 < timeReadout timeUnit setup.graph.period
  shmAngularFrequencyPositive :
    ∀ timeUnit,
      0 < angularFrequencyReadout timeUnit setup.shmAngularFrequency
  circleRadiusPositive :
    ∀ lengthUnit,
      0 < lengthMagnitudeReadout lengthUnit setup.circleRadius
  circleAngularSpeedPositive :
    ∀ timeUnit,
      0 < angularFrequencyReadout timeUnit setup.circleAngularSpeed

/-!
The standard SHM laws with the phase chosen at the crest shown at `t = 0`:
`x(t) = A cos (omega t)` and `omega = 2 pi / T`.  These are general laws and
contain neither the requested radial acceleration nor an answer choice.
-/
structure SatisfiesSimpleHarmonicMotionLaws
    (setup : SHMCircularMotionSetup) : Prop where
  cosinePositionLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit) (t : TimeQuantity),
      signedLengthReadout lengthUnit (setup.graph.position_x t) =
        lengthMagnitudeReadout lengthUnit setup.graph.amplitude *
          Real.cos
            (angularFrequencyReadout timeUnit setup.shmAngularFrequency *
              timeReadout timeUnit t)
  angularFrequencyPeriodLaw :
    ∀ timeUnit : TimeUnit,
      angularFrequencyReadout timeUnit setup.shmAngularFrequency =
        2 * Real.pi / timeReadout timeUnit setup.graph.period

/-!
The projection correspondence between SHM and uniform circular motion: the
circle radius is the SHM amplitude, and both motions share angular frequency.
-/
structure SatisfiesSHMUniformCircularMotionCorrespondence
    (setup : SHMCircularMotionSetup) : Prop where
  circleRadiusEqualsAmplitude :
    setup.circleRadius = setup.graph.amplitude
  angularSpeedEqualsSHMAngularFrequency :
    setup.circleAngularSpeed = setup.shmAngularFrequency

/-!
The centripetal-acceleration magnitude law `a_r = omega^2 r`, stated in every
coherent choice of length and time units.  It is not specialized to the graph's
numerical data or to choice C.
-/
structure SatisfiesUniformCircularMotionRadialAccelerationLaw
    (setup : SHMCircularMotionSetup) : Prop where
  radialAccelerationLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationMagnitudeReadout lengthUnit timeUnit
          setup.radialAccelerationMagnitude =
        angularFrequencyReadout timeUnit setup.circleAngularSpeed ^ 2 *
          lengthMagnitudeReadout lengthUnit setup.circleRadius

/-!
Combining the three governing-law interfaces gives the radial acceleration in
terms of the independently stored graph amplitude and period.  This is a
derived helper conclusion, not a premise field.
-/
lemma radialAcceleration_from_graph_amplitude_and_period
    (setup : SHMCircularMotionSetup)
    (_physical : HasPhysicalParameters setup)
    (_shm : SatisfiesSimpleHarmonicMotionLaws setup)
    (_correspondence :
      SatisfiesSHMUniformCircularMotionCorrespondence setup)
    (_circularLaw :
      SatisfiesUniformCircularMotionRadialAccelerationLaw setup) :
    accelerationInMetersPerSecondSquared
        setup.radialAccelerationMagnitude =
      (2 * Real.pi / timeInSeconds setup.graph.period) ^ 2 *
        lengthInMeters setup.graph.amplitude := by
  rw [accelerationInMetersPerSecondSquared, timeInSeconds, lengthInMeters]
  rw [_circularLaw.radialAccelerationLaw]
  rw [_correspondence.angularSpeedEqualsSHMAngularFrequency,
    _correspondence.circleRadiusEqualsAmplitude]
  rw [_shm.angularFrequencyPeriodLaw]

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate accelerations. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Meter-per-second-squared value printed beside each answer label. -/
def AnswerChoice.metersPerSecondSquared : AnswerChoice → ℝ
  | .A => 1300
  | .B => 1500
  | .C => 1700
  | .D => 1900

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Agreement with an acceleration displayed to the nearest `100 m/s^2`; the
half-unit tolerance is `50 m/s^2` and applies uniformly to every choice.
-/
def MatchesDisplayedAnswer
    (acceleration : AccelerationMagnitudeQuantity)
    (choice : AnswerChoice) : Prop :=
  |accelerationInMetersPerSecondSquared acceleration -
      choice.metersPerSecondSquared| ≤ 50

/-!
The primary graph gives `A = 7 cm` and `T = t_s = 40 ms`.  Therefore the
corresponding circular motion has exact radial acceleration

`(2 pi / 0.040)^2 * 0.070 m/s^2`,

which rounds to `1.7 * 10^3 m/s^2`, answer C.  This formalizes
`thm:physics:phyx_mini_0273:target`.
-/
theorem radialAcceleration_exact_and_matches_choiceC
    (setup : SHMCircularMotionSetup)
    (_problemAndFigure : MatchesProblemAndPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_shm : SatisfiesSimpleHarmonicMotionLaws setup)
    (_correspondence :
      SatisfiesSHMUniformCircularMotionCorrespondence setup)
    (_circularLaw :
      SatisfiesUniformCircularMotionRadialAccelerationLaw setup) :
    accelerationInMetersPerSecondSquared
          setup.radialAccelerationMagnitude =
        (2 * Real.pi / ((40 : ℝ) / 1000)) ^ 2 * ((7 : ℝ) / 100) ∧
      MatchesDisplayedAnswer setup.radialAccelerationMagnitude .C := by
  have length_centimeters_eq (length : LengthMagnitudeQuantity) :
      lengthMagnitudeReadout LengthUnit.centimeters length =
        100 * lengthInMeters length := by
    have h := congrArg (fun value => (value.val : ℝ))
      (length.2
        ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices)
        ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices))
    change lengthMagnitudeReadout LengthUnit.centimeters length =
      _ * lengthInMeters length at h
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.scale,
      LengthUnit.div_eq_val, LengthUnit.meters, NNReal.smul_def] at h ⊢
    exact h
  have time_milliseconds_eq (time : TimeQuantity) :
      timeReadout TimeUnit.milliseconds time =
        1000 * timeInSeconds time := by
    have h := congrArg (fun value => (value.val : ℝ))
      (time.2
        ({UnitChoices.SI with time := TimeUnit.seconds} : UnitChoices)
        ({UnitChoices.SI with time := TimeUnit.milliseconds} : UnitChoices))
    change timeReadout TimeUnit.milliseconds time =
      _ * timeInSeconds time at h
    norm_num [UnitChoices.dimScale, TimeUnit.milliseconds, TimeUnit.scale,
      TimeUnit.div_eq_val, TimeUnit.seconds, NNReal.smul_def] at h ⊢
    exact h
  have hAmplitude :
      lengthInMeters setup.graph.amplitude = (7 : ℝ) / 100 := by
    nlinarith only [_problemAndFigure.amplitudeCentimeters,
      length_centimeters_eq setup.graph.amplitude]
  have hPeriod :
      timeInSeconds setup.graph.period = (40 : ℝ) / 1000 := by
    have hPeriodMilliseconds :
        timeReadout TimeUnit.milliseconds setup.graph.period = 40 := by
      rw [_problemAndFigure.crestToCrestPeriod]
      exact _problemAndFigure.markedTimeMilliseconds
    nlinarith only [hPeriodMilliseconds,
      time_milliseconds_eq setup.graph.period]
  have hAcceleration :=
    radialAcceleration_from_graph_amplitude_and_period setup _physical _shm
      _correspondence _circularLaw
  rw [hPeriod, hAmplitude] at hAcceleration
  constructor
  · exact hAcceleration
  · rw [MatchesDisplayedAnswer, AnswerChoice.metersPerSecondSquared,
      hAcceleration]
    have hpi_lower : (31 : ℝ) / 10 < Real.pi := by
      have hcos0 :
          Real.cos ((31 : ℝ) / 160) ≥ (9811 : ℝ) / 10000 := by
        have hbound :=
          Real.cos_bound (x := (31 : ℝ) / 160)
            (by norm_num [abs_of_nonneg])
        rw [abs_le] at hbound
        norm_num [abs_of_nonneg] at hbound ⊢
        linarith
      have hcos1 :
          Real.cos ((31 : ℝ) / 80) ≥ (9251 : ℝ) / 10000 := by
        have hsquare :=
          pow_le_pow_left₀
            (by norm_num : (0 : ℝ) ≤ 9811 / 10000) hcos0 2
        rw [show (31 : ℝ) / 80 = 2 * (31 / 160) by ring,
          Real.cos_two_mul]
        norm_num at hsquare ⊢
        nlinarith
      have hcos2 :
          Real.cos ((31 : ℝ) / 40) ≥ (7116 : ℝ) / 10000 := by
        have hsquare :=
          pow_le_pow_left₀
            (by norm_num : (0 : ℝ) ≤ 9251 / 10000) hcos1 2
        rw [show (31 : ℝ) / 40 = 2 * (31 / 80) by ring,
          Real.cos_two_mul]
        norm_num at hsquare ⊢
        nlinarith
      have hcos3 : 0 < Real.cos ((31 : ℝ) / 20) := by
        have hsquare :=
          pow_le_pow_left₀
            (by norm_num : (0 : ℝ) ≤ 7116 / 10000) hcos2 2
        rw [show (31 : ℝ) / 20 = 2 * (31 / 40) by ring,
          Real.cos_two_mul]
        norm_num at hsquare ⊢
        nlinarith
      by_contra hnot
      have hroot : Real.pi / 2 ≤ (31 : ℝ) / 20 := by
        nlinarith only [le_of_not_gt hnot]
      have hpoint_le_pi : (31 : ℝ) / 20 ≤ Real.pi := by
        nlinarith only [Real.two_le_pi]
      have hcos_nonpos :
          Real.cos ((31 : ℝ) / 20) ≤ Real.cos (Real.pi / 2) :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          (by positivity) hpoint_le_pi hroot
      rw [Real.cos_pi_div_two] at hcos_nonpos
      linarith
    have hpi_upper : Real.pi < (63 : ℝ) / 20 := by
      have hcos0 :
          Real.cos ((63 : ℝ) / 160) ≤ (4619 : ℝ) / 5000 := by
        have hbound :=
          Real.cos_bound (x := (63 : ℝ) / 160)
            (by norm_num [abs_of_nonneg])
        rw [abs_le] at hbound
        norm_num [abs_of_nonneg] at hbound ⊢
        linarith
      have hcos1 :
          Real.cos ((63 : ℝ) / 80) ≤ (707 : ℝ) / 1000 := by
        have hcos0_nonneg : 0 ≤ Real.cos ((63 : ℝ) / 160) :=
          (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
        have hsquare := pow_le_pow_left₀ hcos0_nonneg hcos0 2
        rw [show (63 : ℝ) / 80 = 2 * (63 / 160) by ring,
          Real.cos_two_mul]
        norm_num at hsquare ⊢
        nlinarith
      have hcos2 : Real.cos ((63 : ℝ) / 40) < 0 := by
        have hcos1_nonneg : 0 ≤ Real.cos ((63 : ℝ) / 80) :=
          (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
        have hsquare := pow_le_pow_left₀ hcos1_nonneg hcos1 2
        rw [show (63 : ℝ) / 40 = 2 * (63 / 80) by ring,
          Real.cos_two_mul]
        norm_num at hsquare ⊢
        nlinarith
      by_contra hnot
      have hpoint_le_root : (63 : ℝ) / 40 ≤ Real.pi / 2 := by
        nlinarith only [le_of_not_gt hnot]
      have hroot_le_pi : Real.pi / 2 ≤ Real.pi := by
        nlinarith only [Real.pi_pos]
      have hcos_nonneg :
          Real.cos (Real.pi / 2) ≤ Real.cos ((63 : ℝ) / 40) :=
        Real.cos_le_cos_of_nonneg_of_le_pi
          (by positivity) hroot_le_pi hpoint_le_root
      rw [Real.cos_pi_div_two] at hcos_nonneg
      linarith
    have hpi_sq_lower : ((31 : ℝ) / 10) ^ 2 < Real.pi ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hpi_lower)
        (by positivity : 0 < Real.pi + (31 : ℝ) / 10)]
    have hpi_sq_upper : Real.pi ^ 2 < ((63 : ℝ) / 20) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hpi_upper)
        (by positivity : 0 < (63 : ℝ) / 20 + Real.pi)]
    rw [abs_le]
    constructor <;>
      norm_num at hpi_sq_lower hpi_sq_upper ⊢ <;>
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0273
