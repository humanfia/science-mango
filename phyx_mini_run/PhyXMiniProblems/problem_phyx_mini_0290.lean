import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0290

open Dimension

/-!
# Transverse velocity from a displacement--time graph

A sinusoidal transverse wave of wavelength `20 cm` travels to the right on a
string.  The primary graph displays the transverse displacement at `x = 0` in
centimeters as a function of time in seconds.  Its vertical scale is
`y_s = 4.0 cm`; the curve starts at equilibrium while rising, reaches a crest
at `2.5 s`, crosses equilibrium while descending at `5.0 s`, reaches a trough
at `7.5 s`, and repeats after `10 s`.

The dimensional quantities below use Physlib's unit-independent
`Dimensionful` type.  Real scalars occur only as named-unit readouts,
dimensionless phases in radians, and displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and coherent unit readouts -/

/-- A nonnegative transverse amplitude. -/
abbrev AmplitudeQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical wavelength. -/
abbrev WavelengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial coordinate or transverse displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed time coordinate relative to the graph's time origin. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- A positive-duration quantity, used here for the wave period. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- Angular frequency, with radians treated as dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Wave number, with radians treated as dimensionless. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A signed transverse-velocity component. -/
abbrev TransverseVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a nonnegative length in the selected unit. -/
def nonnegativeLengthReadout
    (unit : LengthUnit)
    (length : Dimensionful (WithDim L𝓭 NNReal)) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed length coordinate in the selected unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a signed time coordinate in the selected unit. -/
def timeReadout (unit : TimeUnit) (time : TimeQuantity) : ℝ :=
  (time {UnitChoices.SI with time := unit}).val

/-- Read a positive duration in the selected unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read wave number in radians per selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read transverse velocity in a coherent selected length/time unit system. -/
def transverseVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : TransverseVelocityQuantity) : ℝ :=
  (velocity
    {UnitChoices.SI with length := lengthUnit, time := timeUnit}).val

/-! ## Wave roles and primary-figure geometry -/

/-- The disturbance type described in the problem. -/
inductive StringWaveKind where
  | transverseSinusoidal
  deriving DecidableEq, Repr

/-- Propagation direction along the positive-`x` axis. -/
inductive PropagationDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- Sign multiplying the temporal phase in `kx ± omega t + phi`. -/
def temporalPhaseSign : PropagationDirection → ℝ
  | .negativeX => 1
  | .positiveX => -1

/-- The two labeled axes in the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity printed beside each graph axis. -/
inductive AxisQuantity where
  | time_t
  | transverseDisplacement_y
  deriving DecidableEq, Repr

/-- Distinguished points of the plotted sinusoid, ordered from left to right. -/
inductive WaveGraphLandmark where
  | originZero
  | firstCrest
  | descendingZero
  | trough
  | ascendingZero
  | secondCrest
  deriving DecidableEq, Repr

/-!
Labels, units, and landmark coordinates supplied by the primary graph.
`landmarkTime` is dimensionful; the numerical times are recorded separately
in `MatchesPrimaryWaveGraph` rather than built into this structure.
-/
structure DisplacementTimeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  horizontalTimeUnit : TimeUnit
  verticalLengthUnit : LengthUnit
  horizontalAxisShowsUnit : Bool
  verticalAxisShowsUnit : Bool
  verticalScaleYs : AmplitudeQuantity
  horizontalGridIntervalCount : ℕ
  sinusoidalCurveVisible : Bool
  landmarkTime : WaveGraphLandmark → TimeQuantity

/-!
Independent physical quantities and observables for the string wave.
Displacement and transverse velocity remain independent dimensionful fields;
the governing-law premise below relates them to the wave parameters.
-/
structure TravelingStringWaveSetup where
  waveKind : StringWaveKind
  propagationDirection : PropagationDirection
  graph : DisplacementTimeGraph
  wavelength : WavelengthQuantity
  amplitudeYm : AmplitudeQuantity
  period : DurationQuantity
  waveNumber : WaveNumberQuantity
  angularFrequency : AngularFrequencyQuantity
  phaseOffsetRadians : ℝ
  axialOrigin : SignedLengthQuantity
  requestedTime : TimeQuantity
  transverseDisplacement :
    SignedLengthQuantity → TimeQuantity → SignedLengthQuantity
  transverseVelocity :
    SignedLengthQuantity → TimeQuantity → TransverseVelocityQuantity

/-!
Problem-statement data: the disturbance is a right-moving transverse
sinusoid of wavelength `20 cm`, and the requested event is `x = 0`,
`t = 5.0 s`.  No transverse-velocity value occurs in these premises.
-/
structure MatchesStringWaveProblemData
    (setup : TravelingStringWaveSetup) : Prop where
  waveIsTransverseSinusoidal :
    setup.waveKind = .transverseSinusoidal
  propagationIsAlongPositiveX :
    setup.propagationDirection = .positiveX
  wavelengthCentimeters :
    nonnegativeLengthReadout LengthUnit.centimeters setup.wavelength = 20
  requestedPositionIsXZero :
    signedLengthReadout LengthUnit.centimeters setup.axialOrigin = 0
  requestedTimeSeconds :
    timeReadout TimeUnit.seconds setup.requestedTime = 5

/-!
Calibrated evidence from the supplied bitmap.  The five equal horizontal
grid intervals run from `0 s` to the second crest at `12.5 s`; the printed
`10` is at the ascending zero.  Extrema touch `±y_s`, with `y_s = 4 cm`.
The slope signs record what is visibly rising or descending, but give no
numerical velocity answer.
-/
structure MatchesPrimaryWaveGraph
    (setup : TravelingStringWaveSetup) : Prop where
  horizontalAxisLabel :
    setup.graph.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.graph.axisQuantity .vertical = .transverseDisplacement_y
  horizontalUnitIsSeconds :
    setup.graph.horizontalTimeUnit = TimeUnit.seconds
  verticalUnitIsCentimeters :
    setup.graph.verticalLengthUnit = LengthUnit.centimeters
  horizontalUnitPrinted : setup.graph.horizontalAxisShowsUnit = true
  verticalUnitPrinted : setup.graph.verticalAxisShowsUnit = true
  sinusoidalCurveShown : setup.graph.sinusoidalCurveVisible = true
  fiveHorizontalGridIntervals : setup.graph.horizontalGridIntervalCount = 5
  scaleYsCentimeters :
    nonnegativeLengthReadout LengthUnit.centimeters
      setup.graph.verticalScaleYs = 4
  amplitudeTouchesScale :
    nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm =
      nonnegativeLengthReadout LengthUnit.centimeters
        setup.graph.verticalScaleYs
  originTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .originZero) = 0
  firstCrestTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .firstCrest) = 5 / 2
  descendingZeroTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .descendingZero) = 5
  troughTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .trough) = 15 / 2
  ascendingZeroTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .ascendingZero) = 10
  secondCrestTimeSeconds :
    timeReadout TimeUnit.seconds
      (setup.graph.landmarkTime .secondCrest) = 25 / 2
  requestedTimeIsDescendingZero :
    setup.requestedTime = setup.graph.landmarkTime .descendingZero
  periodSeconds : durationReadout TimeUnit.seconds setup.period = 10
  displacementAtOriginZero :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.axialOrigin
          (setup.graph.landmarkTime .originZero)) = 0
  displacementAtFirstCrest :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.axialOrigin
          (setup.graph.landmarkTime .firstCrest)) =
      nonnegativeLengthReadout LengthUnit.centimeters
        setup.graph.verticalScaleYs
  displacementAtDescendingZero :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.axialOrigin
          (setup.graph.landmarkTime .descendingZero)) = 0
  displacementAtTrough :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.axialOrigin
          (setup.graph.landmarkTime .trough)) =
      -(nonnegativeLengthReadout LengthUnit.centimeters
        setup.graph.verticalScaleYs)
  displacementAtAscendingZero :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.axialOrigin
          (setup.graph.landmarkTime .ascendingZero)) = 0
  displacementAtSecondCrest :
    signedLengthReadout LengthUnit.centimeters
        (setup.transverseDisplacement setup.axialOrigin
          (setup.graph.landmarkTime .secondCrest)) =
      nonnegativeLengthReadout LengthUnit.centimeters
        setup.graph.verticalScaleYs
  curveRisesAtOrigin :
    0 < transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
      (setup.transverseVelocity setup.axialOrigin
        (setup.graph.landmarkTime .originZero))
  curveDescendsAtFirstZero :
    transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
        (setup.transverseVelocity setup.axialOrigin
          (setup.graph.landmarkTime .descendingZero)) < 0

/-!
Positivity and the conventional principal representative for phase.  The
phase range does not fix its value; the graph and governing laws select it.
-/
structure HasPhysicalTravelingWaveParameters
    (setup : TravelingStringWaveSetup) : Prop where
  amplitudePositive :
    0 < nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm
  wavelengthPositive :
    0 < nonnegativeLengthReadout LengthUnit.centimeters setup.wavelength
  periodPositive : 0 < durationReadout TimeUnit.seconds setup.period
  waveNumberPositive :
    0 < waveNumberReadout LengthUnit.centimeters setup.waveNumber
  angularFrequencyPositive :
    0 < angularFrequencyReadout TimeUnit.seconds setup.angularFrequency
  phaseNonnegative : 0 ≤ setup.phaseOffsetRadians
  phaseBelowFullTurn : setup.phaseOffsetRadians < 2 * Real.pi

/-!
Generic laws for a sinusoidal traveling string wave:

* `k lambda = 2 pi`;
* `omega T = 2 pi`;
* `y(x,t) = y_m sin(kx ± omega t + phi)`, with the minus sign for travel
  along positive `x`;
* transverse particle velocity is the time derivative of that displacement.

All equations use coherent named-unit readouts.  The velocity law is the
dimensionful observable interface corresponding to Mathlib's scalar
`HasDerivAt.sin` chain rule.  None of these laws mentions the requested event
or a displayed answer value.
-/
structure SatisfiesSinusoidalTravelingWaveLaws
    (setup : TravelingStringWaveSetup) : Prop where
  waveNumberWavelengthRelation :
    ∀ unit : LengthUnit,
      waveNumberReadout unit setup.waveNumber *
          nonnegativeLengthReadout unit setup.wavelength =
        2 * Real.pi
  angularFrequencyPeriodRelation :
    ∀ unit : TimeUnit,
      angularFrequencyReadout unit setup.angularFrequency *
          durationReadout unit setup.period =
        2 * Real.pi
  sinusoidalDisplacementLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (position : SignedLengthQuantity) (time : TimeQuantity),
      signedLengthReadout lengthUnit
          (setup.transverseDisplacement position time) =
        nonnegativeLengthReadout lengthUnit setup.amplitudeYm *
          Real.sin
            (waveNumberReadout lengthUnit setup.waveNumber *
                signedLengthReadout lengthUnit position +
              temporalPhaseSign setup.propagationDirection *
                angularFrequencyReadout timeUnit setup.angularFrequency *
                timeReadout timeUnit time +
              setup.phaseOffsetRadians)
  transverseVelocityLaw :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
        (position : SignedLengthQuantity) (time : TimeQuantity),
      transverseVelocityReadout lengthUnit timeUnit
          (setup.transverseVelocity position time) =
        nonnegativeLengthReadout lengthUnit setup.amplitudeYm *
          temporalPhaseSign setup.propagationDirection *
          angularFrequencyReadout timeUnit setup.angularFrequency *
          Real.cos
            (waveNumberReadout lengthUnit setup.waveNumber *
                signedLengthReadout lengthUnit position +
              temporalPhaseSign setup.propagationDirection *
                angularFrequencyReadout timeUnit setup.angularFrequency *
                timeReadout timeUnit time +
              setup.phaseOffsetRadians)

/-! ## Derived wave parameters and displayed answers -/

/-- Labels of the four velocity choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed transverse velocity in centimeters per second. -/
def displayedVelocityInCentimetersPerSecond : AnswerChoice → ℝ
  | .A => -3 / 2
  | .B => -2
  | .C => -3
  | .D => -5 / 2

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a one-decimal-place displayed velocity. -/
def MatchesDisplayedVelocity
    (velocityCentimetersPerSecond : ℝ) (choice : AnswerChoice) : Prop :=
  |velocityCentimetersPerSecond -
      displayedVelocityInCentimetersPerSecond choice| < 1 / 20

/-- The `10 s` period gives `omega = pi/5 rad/s`. -/
lemma angularFrequencyInRadiansPerSecond_eq_pi_over_five
    (setup : TravelingStringWaveSetup)
    (_figure : MatchesPrimaryWaveGraph setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    angularFrequencyReadout TimeUnit.seconds setup.angularFrequency =
      Real.pi / 5 := by
  have h := _laws.angularFrequencyPeriodRelation TimeUnit.seconds
  rw [_figure.periodSeconds] at h
  linarith

/-!
The stated `20 cm` wavelength gives `k = pi/10 rad/cm`.  This records the
role of wavelength even though the requested particle velocity depends only
on amplitude, angular frequency, and phase at the event.
-/
lemma waveNumberInRadiansPerCentimeter_eq_pi_over_ten
    (setup : TravelingStringWaveSetup)
    (_data : MatchesStringWaveProblemData setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    waveNumberReadout LengthUnit.centimeters setup.waveNumber =
      Real.pi / 10 := by
  have h := _laws.waveNumberWavelengthRelation LengthUnit.centimeters
  rw [_data.wavelengthCentimeters] at h
  linarith

/-!
At the graph origin the displacement vanishes and the curve rises.  For a
right-moving wave written with the problem's sine convention and principal
phase representative, this selects `phi = pi`.
-/
lemma phaseOffsetRadians_eq_pi
    (setup : TravelingStringWaveSetup)
    (_data : MatchesStringWaveProblemData setup)
    (_figure : MatchesPrimaryWaveGraph setup)
    (_physical : HasPhysicalTravelingWaveParameters setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    setup.phaseOffsetRadians = Real.pi := by
  have hdisp := _laws.sinusoidalDisplacementLaw
    LengthUnit.centimeters TimeUnit.seconds setup.axialOrigin
      (setup.graph.landmarkTime .originZero)
  rw [_figure.displacementAtOriginZero, _data.requestedPositionIsXZero,
    _figure.originTimeSeconds, _data.propagationIsAlongPositiveX] at hdisp
  simp only [mul_zero, temporalPhaseSign, neg_mul, one_mul, add_zero,
    zero_add, zero_eq_mul] at hdisp
  have hsin : Real.sin setup.phaseOffsetRadians = 0 :=
    hdisp.resolve_left (ne_of_gt _physical.amplitudePositive)
  have hvel := _laws.transverseVelocityLaw
    LengthUnit.centimeters TimeUnit.seconds setup.axialOrigin
      (setup.graph.landmarkTime .originZero)
  rw [_data.requestedPositionIsXZero, _figure.originTimeSeconds,
    _data.propagationIsAlongPositiveX] at hvel
  simp only [temporalPhaseSign, mul_neg, mul_one, neg_mul, mul_zero,
    one_mul, add_zero, zero_add] at hvel
  have hproduct :
      0 < -(nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm *
        angularFrequencyReadout TimeUnit.seconds setup.angularFrequency *
        Real.cos setup.phaseOffsetRadians) := by
    rw [← hvel]
    exact _figure.curveRisesAtOrigin
  have hpos :
      0 < nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm *
        angularFrequencyReadout TimeUnit.seconds setup.angularFrequency :=
    mul_pos _physical.amplitudePositive _physical.angularFrequencyPositive
  have hcos : Real.cos setup.phaseOffsetRadians < 0 := by
    nlinarith
  rcases Real.sin_eq_zero_iff.mp hsin with ⟨n, hn⟩
  have hn_nonneg_real : (0 : ℝ) ≤ n := by
    nlinarith [_physical.phaseNonnegative, Real.pi_pos]
  have hn_lt_two_real : (n : ℝ) < 2 := by
    nlinarith [_physical.phaseBelowFullTurn, Real.pi_pos]
  have hn_nonneg : (0 : ℤ) ≤ n := by
    exact_mod_cast hn_nonneg_real
  have hn_lt_two : n < 2 := by
    exact_mod_cast hn_lt_two_real
  have hn_zero_or_one : n = 0 ∨ n = 1 := by
    omega
  rcases hn_zero_or_one with rfl | rfl
  · norm_num at hn
    norm_num [← hn] at hcos
  · norm_num at hn ⊢
    exact hn.symm

/-!
At `x = 0`, `t = 5 s`, the phase is zero modulo a full turn and the exact
model velocity is `-4 pi / 5 cm/s`.
-/
lemma transverseVelocityAtFiveSeconds_exact
    (setup : TravelingStringWaveSetup)
    (_data : MatchesStringWaveProblemData setup)
    (_figure : MatchesPrimaryWaveGraph setup)
    (_physical : HasPhysicalTravelingWaveParameters setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
        (setup.transverseVelocity setup.axialOrigin setup.requestedTime) =
      -(4 * Real.pi / 5) := by
  have hamp :
      nonnegativeLengthReadout LengthUnit.centimeters setup.amplitudeYm = 4 :=
    _figure.amplitudeTouchesScale.trans _figure.scaleYsCentimeters
  have homega :=
    angularFrequencyInRadiansPerSecond_eq_pi_over_five setup _figure _laws
  have hphase :=
    phaseOffsetRadians_eq_pi setup _data _figure _physical _laws
  rw [_laws.transverseVelocityLaw LengthUnit.centimeters TimeUnit.seconds
    setup.axialOrigin setup.requestedTime]
  rw [_data.propagationIsAlongPositiveX, _data.requestedPositionIsXZero,
    _data.requestedTimeSeconds, hamp, homega, hphase]
  simp [temporalPhaseSign]
  ring

/-!
The exact transverse velocity is `-4 pi / 5 cm/s`, approximately
`-2.51 cm/s`.  It therefore rounds to `-2.5 cm/s`, choice D, and is at least
as close to D as to every other displayed choice.

This formalizes `thm:physics:phyx_mini_0290:target`.
-/
theorem problem_phyx_mini_0290
    (setup : TravelingStringWaveSetup)
    (_data : MatchesStringWaveProblemData setup)
    (_figure : MatchesPrimaryWaveGraph setup)
    (_physical : HasPhysicalTravelingWaveParameters setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
        (setup.transverseVelocity setup.axialOrigin setup.requestedTime) =
        -(4 * Real.pi / 5) ∧
      MatchesDisplayedVelocity
        (transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
          (setup.transverseVelocity setup.axialOrigin setup.requestedTime))
        recordedDatasetAnswer ∧
      ∀ choice : AnswerChoice,
        |transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
              (setup.transverseVelocity setup.axialOrigin setup.requestedTime) -
            displayedVelocityInCentimetersPerSecond recordedDatasetAnswer| ≤
          |transverseVelocityReadout LengthUnit.centimeters TimeUnit.seconds
              (setup.transverseVelocity setup.axialOrigin setup.requestedTime) -
            displayedVelocityInCentimetersPerSecond choice| := by
  have hvelocity :=
    transverseVelocityAtFiveSeconds_exact setup _data _figure _physical _laws
  have hlo : (49 : ℝ) / 16 < Real.pi := by
    have hs49 : Real.sin ((49 : ℝ) / 128) < 3 / 8 := by
      have h := Real.sin_bound (x := (49 : ℝ) / 128) (by norm_num)
      have hu := (abs_le.mp h).2
      norm_num at hu ⊢
      nlinarith
    have hsPi : 3 / 8 < Real.sin (Real.pi / 8) := by
      rw [Real.sin_pi_div_eight]
      have hr_nonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
      have hr_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      have hr_lt : Real.sqrt (2 : ℝ) < 23 / 16 := by
        nlinarith
      have hi_nonneg : 0 ≤ 2 - Real.sqrt (2 : ℝ) := by
        nlinarith
      have hs_nonneg :
          0 ≤ Real.sqrt (2 - Real.sqrt (2 : ℝ)) :=
        Real.sqrt_nonneg _
      have hs_sq :
          Real.sqrt (2 - Real.sqrt (2 : ℝ)) ^ 2 =
            2 - Real.sqrt 2 :=
        Real.sq_sqrt hi_nonneg
      nlinarith
    have hangle : (49 : ℝ) / 128 < Real.pi / 8 := by
      by_contra h
      have hle : Real.pi / 8 ≤ (49 : ℝ) / 128 := le_of_not_gt h
      have hsle := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := Real.pi / 8) (y := (49 : ℝ) / 128)
        (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.one_le_pi_div_two]) hle
      linarith
    nlinarith
  have hhi : Real.pi < (51 : ℝ) / 16 := by
    have hsPi : Real.sin (Real.pi / 8) < (49 : ℝ) / 128 := by
      rw [Real.sin_pi_div_eight]
      have hr_nonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
      have hr_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      have hr_gt : 5791 / 4096 < Real.sqrt (2 : ℝ) := by
        nlinarith
      have hr_le_two : Real.sqrt (2 : ℝ) ≤ 2 := by
        nlinarith
      have hi_nonneg : 0 ≤ 2 - Real.sqrt (2 : ℝ) := by
        linarith
      have hs_nonneg :
          0 ≤ Real.sqrt (2 - Real.sqrt (2 : ℝ)) :=
        Real.sqrt_nonneg _
      have hs_sq :
          Real.sqrt (2 - Real.sqrt (2 : ℝ)) ^ 2 =
            2 - Real.sqrt 2 :=
        Real.sq_sqrt hi_nonneg
      nlinarith
    have hs51 : (49 : ℝ) / 128 < Real.sin ((51 : ℝ) / 128) := by
      have h := Real.sin_bound (x := (51 : ℝ) / 128) (by norm_num)
      have hl := (abs_le.mp h).1
      norm_num at hl ⊢
      nlinarith
    have hangle : Real.pi / 8 < (51 : ℝ) / 128 := by
      by_contra h
      have hle : (51 : ℝ) / 128 ≤ Real.pi / 8 := le_of_not_gt h
      have hsle := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := (51 : ℝ) / 128) (y := Real.pi / 8)
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) hle
      linarith
    nlinarith
  have hclose :
      |-(4 * Real.pi / 5) -
        displayedVelocityInCentimetersPerSecond recordedDatasetAnswer| <
        1 / 20 := by
    rw [abs_lt]
    constructor <;>
      norm_num [displayedVelocityInCentimetersPerSecond,
        recordedDatasetAnswer] <;>
      nlinarith
  refine ⟨hvelocity, ?_, ?_⟩
  · simpa [MatchesDisplayedVelocity, hvelocity] using hclose
  · intro choice
    rw [hvelocity]
    cases choice with
    | D => rfl
    | A =>
        apply hclose.le.trans
        rw [abs_of_nonpos]
        · norm_num [displayedVelocityInCentimetersPerSecond]
          nlinarith
        · norm_num [displayedVelocityInCentimetersPerSecond]
          nlinarith
    | B =>
        apply hclose.le.trans
        rw [abs_of_nonpos]
        · norm_num [displayedVelocityInCentimetersPerSecond]
          nlinarith
        · norm_num [displayedVelocityInCentimetersPerSecond]
          nlinarith
    | C =>
        apply hclose.le.trans
        rw [abs_of_nonneg]
        · norm_num [displayedVelocityInCentimetersPerSecond]
          nlinarith
        · norm_num [displayedVelocityInCentimetersPerSecond]
          nlinarith

end PhyXMiniProblems.ProblemPhyXMini0290
