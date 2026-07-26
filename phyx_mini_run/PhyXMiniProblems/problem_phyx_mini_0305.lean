import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0305

open Dimension

/-!
# Amplitude of a sinusoidal string wave from a transverse-velocity graph

A transverse sinusoidal wave of wavelength `20 cm` travels along the positive
`x` direction.  The primary figure plots the transverse velocity `u` of the
string particle at `x = 0` against time `t`.  Its labeled velocity scale is
`u_s = 5.0 cm/s`.  The curve passes through zero at `0 s`, reaches `+u_s` at
`1 s`, passes through zero at `2 s`, reaches `-u_s` at `3 s`, and completes
the cycle at `4 s`.

Physlib's `Dimensionful` type represents the physical wavelength, amplitude,
period, wave number, angular frequency, and transverse speeds.  Real numbers
below are used only for coherent named-unit readouts, measured time
coordinates in seconds, dimensionless phases, and displayed answer values.
-/

/-! ## Dimensionful wave quantities and coherent readouts -/

/-- A nonnegative physical length, used for wavelength and amplitude. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial coordinate or transverse displacement. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev DurationMagnitude : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative wave number, with radians treated as dimensionless. -/
abbrev WaveNumberMagnitude : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A nonnegative angular frequency, with radians treated as dimensionless. -/
abbrev AngularFrequencyMagnitude : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative transverse-speed magnitude. -/
abbrev SpeedMagnitude : Type := DimSpeed

/-- A signed transverse-velocity component. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a nonnegative length in a selected length unit. -/
def lengthMagnitudeReadout
    (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed coordinate or displacement in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read a duration in a selected time unit. -/
def durationReadout
    (unit : TimeUnit) (duration : DurationMagnitude) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read wave number in radians per selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberMagnitude) : ℝ :=
  ((waveNumber {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyMagnitude) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed magnitude in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedMagnitude) : ℝ :=
  ((speed {UnitChoices.SI with
      length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read signed transverse velocity in coherent selected units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
      length := lengthUnit, time := timeUnit}).val

/-! ## Physical roles and primary-figure labels -/

/-- The disturbance type stated in the problem. -/
inductive WaveKind where
  | transverseSinusoidal
  deriving DecidableEq, Repr

/-- Propagation direction along the horizontal string axis. -/
inductive PropagationDirection where
  | negativeX
  | positiveX
  deriving DecidableEq, Repr

/-- Sign multiplying `omega t` in a traveling-wave phase. -/
def temporalPhaseSign : PropagationDirection → ℝ
  | .negativeX => 1
  | .positiveX => -1

/-- The two coordinate axes drawn in the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical quantity printed beside each graph axis. -/
inductive AxisQuantity where
  | time_t
  | transverseVelocity_u
  deriving DecidableEq, Repr

/-- Distinguished velocity-curve landmarks, ordered from left to right. -/
inductive VelocityGraphLandmark where
  | originZero
  | positivePeak
  | descendingZero
  | negativeTrough
  | cycleEndZero
  deriving DecidableEq, Repr

/-!
The labels, units, calibration, and landmark observables carried by the
primary velocity-versus-time graph.  The landmark times are real scalar
readouts explicitly measured in the printed unit `seconds`; marked velocities
remain dimensionful physical quantities.
-/
structure TransverseVelocityTimeGraph where
  axisQuantity : GraphAxis → AxisQuantity
  horizontalTimeUnit : TimeUnit
  verticalLengthUnit : LengthUnit
  verticalTimeUnit : TimeUnit
  velocityScaleUs : SpeedMagnitude
  horizontalGridIntervalCount : ℕ
  sinusoidalCurveVisible : Bool
  landmarkTimeInSeconds : VelocityGraphLandmark → ℝ
  markedVelocity : VelocityGraphLandmark → SignedVelocityQuantity

/-!
Independent parameters and observables of the traveling string wave.
Neither the displacement amplitude nor its numerical readout is defined from
the requested answer.  Governing-law premises below relate these fields.
-/
structure SinusoidalStringWaveSetup where
  waveKind : WaveKind
  propagationDirection : PropagationDirection
  graph : TransverseVelocityTimeGraph
  observationPosition : SignedLengthQuantity
  wavelength : LengthMagnitude
  displacementAmplitude : LengthMagnitude
  period : DurationMagnitude
  waveNumber : WaveNumberMagnitude
  angularFrequency : AngularFrequencyMagnitude
  phaseOffsetRadians : ℝ
  displacementAtSeconds :
    SignedLengthQuantity → ℝ → SignedLengthQuantity
  transverseVelocityAtSeconds :
    SignedLengthQuantity → ℝ → SignedVelocityQuantity
  maximumTransverseSpeed : SpeedMagnitude

/-!
Problem-statement data independent of the requested amplitude: the wave is a
right-moving transverse sinusoid of wavelength `20 cm`, observed at `x = 0`.
-/
structure MatchesWaveProblemData
    (setup : SinusoidalStringWaveSetup) : Prop where
  waveIsTransverseSinusoidal :
    setup.waveKind = .transverseSinusoidal
  propagationIsAlongPositiveX :
    setup.propagationDirection = .positiveX
  wavelengthCentimeters :
    lengthMagnitudeReadout LengthUnit.centimeters setup.wavelength = 20
  observationPositionIsXZero :
    signedLengthReadout LengthUnit.centimeters setup.observationPosition = 0

/-!
Calibrated evidence from the supplied bitmap.  The four equal horizontal
intervals cover one cycle from `0 s` through `4 s`; the curve touches
`+u_s` at `1 s` and `-u_s` at `3 s`, where `u_s = 5 cm/s`.

These are figure/data readouts.  In particular, this structure does not give
the displacement amplitude or select an answer choice.
-/
structure MatchesPrimaryVelocityGraph
    (setup : SinusoidalStringWaveSetup) : Prop where
  horizontalAxisLabel :
    setup.graph.axisQuantity .horizontal = .time_t
  verticalAxisLabel :
    setup.graph.axisQuantity .vertical = .transverseVelocity_u
  horizontalUnitIsSeconds :
    setup.graph.horizontalTimeUnit = TimeUnit.seconds
  verticalLengthUnitIsCentimeters :
    setup.graph.verticalLengthUnit = LengthUnit.centimeters
  verticalTimeUnitIsSeconds :
    setup.graph.verticalTimeUnit = TimeUnit.seconds
  sinusoidalCurveShown : setup.graph.sinusoidalCurveVisible = true
  fourHorizontalGridIntervals : setup.graph.horizontalGridIntervalCount = 4
  scaleUsCentimetersPerSecond :
    speedReadout LengthUnit.centimeters TimeUnit.seconds
      setup.graph.velocityScaleUs = 5
  originTimeSeconds :
    setup.graph.landmarkTimeInSeconds .originZero = 0
  positivePeakTimeSeconds :
    setup.graph.landmarkTimeInSeconds .positivePeak = 1
  descendingZeroTimeSeconds :
    setup.graph.landmarkTimeInSeconds .descendingZero = 2
  negativeTroughTimeSeconds :
    setup.graph.landmarkTimeInSeconds .negativeTrough = 3
  cycleEndTimeSeconds :
    setup.graph.landmarkTimeInSeconds .cycleEndZero = 4
  originVelocityReadout :
    signedVelocityReadout LengthUnit.centimeters TimeUnit.seconds
      (setup.graph.markedVelocity .originZero) = 0
  positivePeakVelocityReadout :
    signedVelocityReadout LengthUnit.centimeters TimeUnit.seconds
      (setup.graph.markedVelocity .positivePeak) = 5
  descendingZeroVelocityReadout :
    signedVelocityReadout LengthUnit.centimeters TimeUnit.seconds
      (setup.graph.markedVelocity .descendingZero) = 0
  negativeTroughVelocityReadout :
    signedVelocityReadout LengthUnit.centimeters TimeUnit.seconds
      (setup.graph.markedVelocity .negativeTrough) = -5
  cycleEndVelocityReadout :
    signedVelocityReadout LengthUnit.centimeters TimeUnit.seconds
      (setup.graph.markedVelocity .cycleEndZero) = 0
  landmarksOccurOnVelocityCurve :
    ∀ landmark : VelocityGraphLandmark,
      setup.transverseVelocityAtSeconds setup.observationPosition
          (setup.graph.landmarkTimeInSeconds landmark) =
        setup.graph.markedVelocity landmark
  peakTouchesScale :
    signedVelocityReadout LengthUnit.centimeters TimeUnit.seconds
        (setup.graph.markedVelocity .positivePeak) =
      speedReadout LengthUnit.centimeters TimeUnit.seconds
        setup.graph.velocityScaleUs
  graphScaleIsMaximumSpeed :
    speedReadout LengthUnit.centimeters TimeUnit.seconds
        setup.maximumTransverseSpeed =
      speedReadout LengthUnit.centimeters TimeUnit.seconds
        setup.graph.velocityScaleUs
  oneCyclePeriodSeconds :
    durationReadout TimeUnit.seconds setup.period =
      setup.graph.landmarkTimeInSeconds .cycleEndZero -
        setup.graph.landmarkTimeInSeconds .originZero
  periodSeconds : durationReadout TimeUnit.seconds setup.period = 4

/-! Positivity conditions for the nondegenerate wave shown in the graph. -/
structure HasPhysicalWaveParameters
    (setup : SinusoidalStringWaveSetup) : Prop where
  displacementAmplitudePositive :
    0 < lengthMagnitudeReadout LengthUnit.centimeters
      setup.displacementAmplitude
  wavelengthPositive :
    0 < lengthMagnitudeReadout LengthUnit.centimeters setup.wavelength
  periodPositive : 0 < durationReadout TimeUnit.seconds setup.period
  waveNumberPositive :
    0 < waveNumberReadout LengthUnit.centimeters setup.waveNumber
  angularFrequencyPositive :
    0 < angularFrequencyReadout TimeUnit.seconds setup.angularFrequency
  maximumTransverseSpeedPositive :
    0 < speedReadout LengthUnit.centimeters TimeUnit.seconds
      setup.maximumTransverseSpeed

/-!
Generic governing laws for a sinusoidal traveling string wave:

* `k lambda = 2 pi`;
* `omega T = 2 pi`;
* `y(x,t) = A sin(kx ± omega t + phi)`, with the minus sign for positive-`x`
  propagation;
* transverse particle velocity is the time derivative of displacement;
* the separately represented maximum transverse speed bounds the velocity
  magnitude and is attained.

The derivative interface is grounded by Mathlib's `HasDerivAt` API.  No field
states a numerical displacement amplitude or one of the displayed answers.
-/
structure SatisfiesSinusoidalTravelingWaveLaws
    (setup : SinusoidalStringWaveSetup) : Prop where
  waveNumberWavelengthRelation :
    ∀ unit : LengthUnit,
      waveNumberReadout unit setup.waveNumber *
          lengthMagnitudeReadout unit setup.wavelength =
        2 * Real.pi
  angularFrequencyPeriodRelation :
    ∀ unit : TimeUnit,
      angularFrequencyReadout unit setup.angularFrequency *
          durationReadout unit setup.period =
        2 * Real.pi
  sinusoidalDisplacementLaw :
    ∀ (lengthUnit : LengthUnit) (position : SignedLengthQuantity)
        (timeInSeconds : ℝ),
      signedLengthReadout lengthUnit
          (setup.displacementAtSeconds position timeInSeconds) =
        lengthMagnitudeReadout lengthUnit setup.displacementAmplitude *
          Real.sin
            (waveNumberReadout LengthUnit.centimeters setup.waveNumber *
                signedLengthReadout LengthUnit.centimeters position +
              temporalPhaseSign setup.propagationDirection *
                angularFrequencyReadout TimeUnit.seconds
                  setup.angularFrequency * timeInSeconds +
              setup.phaseOffsetRadians)
  transverseVelocityIsTimeDerivative :
    ∀ (lengthUnit : LengthUnit) (position : SignedLengthQuantity)
        (timeInSeconds : ℝ),
      HasDerivAt
        (fun time ↦
          signedLengthReadout lengthUnit
            (setup.displacementAtSeconds position time))
        (signedVelocityReadout lengthUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position timeInSeconds))
        timeInSeconds
  maximumSpeedBoundsVelocity :
    ∀ (lengthUnit : LengthUnit) (position : SignedLengthQuantity)
        (timeInSeconds : ℝ),
      |signedVelocityReadout lengthUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position timeInSeconds)| ≤
        speedReadout lengthUnit TimeUnit.seconds
          setup.maximumTransverseSpeed
  maximumSpeedIsAttained :
    ∀ (lengthUnit : LengthUnit) (position : SignedLengthQuantity),
      ∃ timeInSeconds : ℝ,
        |signedVelocityReadout lengthUnit TimeUnit.seconds
            (setup.transverseVelocityAtSeconds position timeInSeconds)| =
          speedReadout lengthUnit TimeUnit.seconds
            setup.maximumTransverseSpeed

/-! ## Derived quantities and displayed answers -/

/-- The `4 s` cycle gives `omega = pi/2 rad/s`. -/
lemma angularFrequencyInRadiansPerSecond_eq_pi_over_two
    (setup : SinusoidalStringWaveSetup)
    (_figure : MatchesPrimaryVelocityGraph setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    angularFrequencyReadout TimeUnit.seconds setup.angularFrequency =
      Real.pi / 2 := by
  have hperiod :=
    _laws.angularFrequencyPeriodRelation TimeUnit.seconds
  rw [_figure.periodSeconds] at hperiod
  linarith

/-!
The stated `20 cm` wavelength gives `k = pi/10 rad/cm`.  Wavelength does not
enter the final amplitude calculation at a fixed string point, but this lemma
records its physical role in the traveling-wave model.
-/
lemma waveNumberInRadiansPerCentimeter_eq_pi_over_ten
    (setup : SinusoidalStringWaveSetup)
    (_data : MatchesWaveProblemData setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    waveNumberReadout LengthUnit.centimeters setup.waveNumber =
      Real.pi / 10 := by
  have hwavelength :=
    _laws.waveNumberWavelengthRelation LengthUnit.centimeters
  rw [_data.wavelengthCentimeters] at hwavelength
  linarith

/-!
Differentiating the sinusoidal displacement and using that `|cos|` attains
one shows that the transverse-speed amplitude is `omega A`.  This is a
derived lemma rather than a premise field.
-/
lemma maximumTransverseSpeed_eq_angularFrequency_mul_amplitude
    (setup : SinusoidalStringWaveSetup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup)
    (lengthUnit : LengthUnit) :
    speedReadout lengthUnit TimeUnit.seconds
        setup.maximumTransverseSpeed =
      angularFrequencyReadout TimeUnit.seconds setup.angularFrequency *
        lengthMagnitudeReadout lengthUnit setup.displacementAmplitude := by
  let A :=
    lengthMagnitudeReadout lengthUnit setup.displacementAmplitude
  let omega :=
    angularFrequencyReadout TimeUnit.seconds setup.angularFrequency
  let maximumSpeed :=
    speedReadout lengthUnit TimeUnit.seconds setup.maximumTransverseSpeed
  have hA : 0 ≤ A := by
    dsimp [A, lengthMagnitudeReadout]
    positivity
  have homega : 0 ≤ omega := by
    dsimp [omega, angularFrequencyReadout]
    positivity
  have hmaximumSpeed : 0 ≤ maximumSpeed := by
    dsimp [maximumSpeed, speedReadout]
    positivity
  have velocity_formula
      (position : SignedLengthQuantity) (time : ℝ) :
      signedVelocityReadout lengthUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position time) =
        A *
          (Real.cos
              (waveNumberReadout LengthUnit.centimeters setup.waveNumber *
                    signedLengthReadout LengthUnit.centimeters position +
                temporalPhaseSign setup.propagationDirection * omega * time +
                setup.phaseOffsetRadians) *
            (temporalPhaseSign setup.propagationDirection * omega)) := by
    have hactual :=
      _laws.transverseVelocityIsTimeDerivative lengthUnit position time
    have hinner :
        HasDerivAt
          (fun t : ℝ =>
            waveNumberReadout LengthUnit.centimeters setup.waveNumber *
                  signedLengthReadout LengthUnit.centimeters position +
              temporalPhaseSign setup.propagationDirection * omega * t +
              setup.phaseOffsetRadians)
          (temporalPhaseSign setup.propagationDirection * omega) time := by
      simpa only [id_eq, mul_one] using
        (((HasDerivAt.const_mul
            (temporalPhaseSign setup.propagationDirection * omega)
            (hasDerivAt_id time)).const_add
              (waveNumberReadout LengthUnit.centimeters setup.waveNumber *
                signedLengthReadout LengthUnit.centimeters position)).add_const
                  setup.phaseOffsetRadians)
    have hmodel := HasDerivAt.const_mul A hinner.sin
    have heventually :
        (fun t : ℝ =>
            signedLengthReadout lengthUnit
              (setup.displacementAtSeconds position t)) =ᶠ[nhds time]
          (fun t : ℝ =>
            A * Real.sin
              (waveNumberReadout LengthUnit.centimeters setup.waveNumber *
                    signedLengthReadout LengthUnit.centimeters position +
                temporalPhaseSign setup.propagationDirection * omega * t +
                setup.phaseOffsetRadians)) := by
      filter_upwards [] with t
      exact
        _laws.sinusoidalDisplacementLaw lengthUnit position t
    exact hactual.unique (hmodel.congr_of_eventuallyEq heventually)
  have hupper : maximumSpeed ≤ omega * A := by
    rcases
        _laws.maximumSpeedIsAttained
          lengthUnit setup.observationPosition with
      ⟨time, htime⟩
    rw [velocity_formula] at htime
    calc
      maximumSpeed =
          |A *
            (Real.cos
                (waveNumberReadout LengthUnit.centimeters setup.waveNumber *
                      signedLengthReadout LengthUnit.centimeters
                        setup.observationPosition +
                    temporalPhaseSign setup.propagationDirection * omega *
                      time +
                    setup.phaseOffsetRadians) *
              (temporalPhaseSign setup.propagationDirection * omega))| :=
        htime.symm
      _ =
          A *
            (|Real.cos
                (waveNumberReadout LengthUnit.centimeters setup.waveNumber *
                      signedLengthReadout LengthUnit.centimeters
                        setup.observationPosition +
                    temporalPhaseSign setup.propagationDirection * omega *
                      time +
                    setup.phaseOffsetRadians)| * omega) := by
        simp only [abs_mul]
        rw [abs_of_nonneg hA, abs_of_nonneg homega]
        cases setup.propagationDirection <;>
          simp [temporalPhaseSign]
      _ ≤ A * (1 * omega) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (Real.abs_cos_le_one _) homega)
            hA
      _ = omega * A := by ring
  have hlower : omega * A ≤ maximumSpeed := by
    by_cases homegaZero : omega = 0
    · simp [homegaZero, hmaximumSpeed]
    · have hsign :
          temporalPhaseSign setup.propagationDirection ≠ 0 := by
        cases setup.propagationDirection <;>
          norm_num [temporalPhaseSign]
      have hdenominator :
          temporalPhaseSign setup.propagationDirection * omega ≠ 0 :=
        mul_ne_zero hsign homegaZero
      let phaseConstant :=
        waveNumberReadout LengthUnit.centimeters setup.waveNumber *
            signedLengthReadout LengthUnit.centimeters
              setup.observationPosition +
          setup.phaseOffsetRadians
      let timeAtUnitCosine :=
        -phaseConstant /
          (temporalPhaseSign setup.propagationDirection * omega)
      have hphase :
          waveNumberReadout LengthUnit.centimeters setup.waveNumber *
                signedLengthReadout LengthUnit.centimeters
                  setup.observationPosition +
              temporalPhaseSign setup.propagationDirection * omega *
                timeAtUnitCosine +
              setup.phaseOffsetRadians =
            0 := by
        dsimp [timeAtUnitCosine, phaseConstant]
        field_simp [hdenominator]
        ring
      have hbound :=
        _laws.maximumSpeedBoundsVelocity
          lengthUnit setup.observationPosition timeAtUnitCosine
      rw [velocity_formula, hphase] at hbound
      cases hdirection : setup.propagationDirection <;>
        simp only [hdirection, temporalPhaseSign, Real.cos_zero, one_mul,
          abs_mul, abs_neg, abs_one] at hbound <;>
        rw [abs_of_nonneg hA, abs_of_nonneg homega] at hbound <;>
        simpa [maximumSpeed, mul_comm] using hbound
  change maximumSpeed = omega * A
  exact le_antisymm hupper hlower

/-!
The graph gives maximum transverse speed `5 cm/s` and period `4 s`, hence
`omega = pi/2 rad/s`.  Solving `u_max = omega A` gives the exact displacement
amplitude `A = 10/pi cm`.
-/
lemma displacementAmplitudeInCentimeters_eq_ten_div_pi
    (setup : SinusoidalStringWaveSetup)
    (_figure : MatchesPrimaryVelocityGraph setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    lengthMagnitudeReadout LengthUnit.centimeters
        setup.displacementAmplitude =
      10 / Real.pi := by
  have hfrequency :=
    angularFrequencyInRadiansPerSecond_eq_pi_over_two
      setup _figure _laws
  have hmaximum :=
    maximumTransverseSpeed_eq_angularFrequency_mul_amplitude
      setup _laws LengthUnit.centimeters
  have hspeed :
      speedReadout LengthUnit.centimeters TimeUnit.seconds
          setup.maximumTransverseSpeed =
        5 :=
    _figure.graphScaleIsMaximumSpeed.trans
      _figure.scaleUsCentimetersPerSecond
  rw [hspeed, hfrequency] at hmaximum
  apply (eq_div_iff (ne_of_gt Real.pi_pos)).2
  nlinarith

/-- Labels of the four amplitude choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed displacement amplitude in centimeters. -/
def displayedAmplitudeInCentimeters : AnswerChoice → ℝ
  | .A => 2
  | .B => 12 / 5
  | .C => 14 / 5
  | .D => 16 / 5

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with an amplitude displayed to the nearest tenth of a centimeter. -/
def MatchesDisplayedAmplitude
    (amplitudeCentimeters : ℝ) (choice : AnswerChoice) : Prop :=
  |amplitudeCentimeters - displayedAmplitudeInCentimeters choice| < 1 / 20

/-!
The exact amplitude is `10/pi cm`, approximately `3.18 cm`; it rounds to
`3.2 cm`, choice D, and is no farther from D than from any other displayed
choice.

This formalizes `thm:physics:phyx_mini_0305:target`.
-/
theorem problem_phyx_mini_0305
    (setup : SinusoidalStringWaveSetup)
    (_data : MatchesWaveProblemData setup)
    (_figure : MatchesPrimaryVelocityGraph setup)
    (_physical : HasPhysicalWaveParameters setup)
    (_laws : SatisfiesSinusoidalTravelingWaveLaws setup) :
    lengthMagnitudeReadout LengthUnit.centimeters
        setup.displacementAmplitude =
        10 / Real.pi ∧
      MatchesDisplayedAmplitude
        (lengthMagnitudeReadout LengthUnit.centimeters
          setup.displacementAmplitude)
        recordedDatasetAnswer ∧
      ∀ choice : AnswerChoice,
        |lengthMagnitudeReadout LengthUnit.centimeters
              setup.displacementAmplitude -
            displayedAmplitudeInCentimeters recordedDatasetAnswer| ≤
          |lengthMagnitudeReadout LengthUnit.centimeters
              setup.displacementAmplitude -
            displayedAmplitudeInCentimeters choice| := by
  have hamplitude :=
    displacementAmplitudeInCentimeters_eq_ten_div_pi
      setup _figure _physical _laws
  let x : ℝ := Real.pi / 6
  have hxPositive : 0 < x := by
    dsimp [x]
    positivity
  have hxAtMostOne : x ≤ 1 := by
    dsimp [x]
    nlinarith [Real.pi_le_four]
  have hsineBound :=
    Real.sin_bound
      (x := x) (abs_le.mpr ⟨by linarith, hxAtMostOne⟩)
  have hsineValue : Real.sin x = 1 / 2 := by
    dsimp [x]
    exact Real.sin_pi_div_six
  rw [hsineValue, abs_of_pos hxPositive] at hsineBound
  have hsineLower :=
    (abs_le.mp hsineBound).2
  have hsineUpper :=
    (abs_le.mp hsineBound).1
  have hpiGreaterThanThree : 3 < Real.pi := by
    by_contra hpi
    have hxAtMostHalf : x ≤ 1 / 2 := by
      dsimp [x]
      nlinarith
    have hfirst : 0 ≤ 1 / 2 - x := by
      linarith
    have hsecond :
        0 < x ^ 3 / 6 - 5 * x ^ 4 / 96 := by
      have hcube : 0 < x ^ 3 := pow_pos hxPositive 3
      have hfactor : 0 < 16 - 5 * x := by
        nlinarith
      have hproduct : 0 < x ^ 3 * (16 - 5 * x) :=
        mul_pos hcube hfactor
      nlinarith
    nlinarith
  have hpiLower : (40 / 13 : ℝ) < Real.pi := by
    by_contra hpi
    have hxAtMost : x ≤ 20 / 39 := by
      dsimp [x]
      nlinarith
    have hxAtLeastHalf : (1 / 2 : ℝ) ≤ x := by
      dsimp [x]
      nlinarith
    have hcube : (1 / 2 : ℝ) ^ 3 ≤ x ^ 3 := by
      gcongr
    have hfourth : x ^ 4 ≤ (20 / 39 : ℝ) ^ 4 := by
      gcongr
    have hnumerical :
        0 <
          (1 / 2 : ℝ) - 20 / 39 + (1 / 2 : ℝ) ^ 3 / 6 -
            5 * (20 / 39 : ℝ) ^ 4 / 96 := by
      norm_num
    nlinarith
  have hpiUpper : Real.pi < (200 / 63 : ℝ) := by
    by_contra hpi
    have hxAtLeast : (100 / 189 : ℝ) ≤ x := by
      dsimp [x]
      nlinarith
    have hxAtMostTwoThirds : x ≤ 2 / 3 := by
      dsimp [x]
      nlinarith [Real.pi_le_four]
    have hxNonnegative : 0 ≤ x := hxPositive.le
    have hxSquared : x ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by
      gcongr
    have hxCubed : x ^ 3 ≤ (2 / 3 : ℝ) ^ 3 := by
      gcongr
    let c : ℝ := 100 / 189
    have hcNonnegative : 0 ≤ c := by
      norm_num [c]
    have hcAtMostTwoThirds : c ≤ 2 / 3 := by
      norm_num [c]
    have hxxc : x * c ≤ (2 / 3 : ℝ) ^ 2 := by
      calc
        x * c ≤ (2 / 3) * c :=
          mul_le_mul_of_nonneg_right hxAtMostTwoThirds hcNonnegative
        _ ≤ (2 / 3) * (2 / 3) :=
          mul_le_mul_of_nonneg_left hcAtMostTwoThirds (by norm_num)
        _ = (2 / 3 : ℝ) ^ 2 := by ring
    have hxcSquared : x * c ^ 2 ≤ (2 / 3 : ℝ) ^ 3 := by
      calc
        x * c ^ 2 ≤ (2 / 3) * c ^ 2 :=
          mul_le_mul_of_nonneg_right hxAtMostTwoThirds (sq_nonneg c)
        _ ≤ (2 / 3) * (2 / 3) ^ 2 := by
          gcongr
        _ = (2 / 3 : ℝ) ^ 3 := by ring
    have hxSquaredc : x ^ 2 * c ≤ (2 / 3 : ℝ) ^ 3 := by
      calc
        x ^ 2 * c ≤ (2 / 3) ^ 2 * c :=
          mul_le_mul_of_nonneg_right hxSquared hcNonnegative
        _ ≤ (2 / 3) ^ 2 * (2 / 3) := by
          gcongr
        _ = (2 / 3 : ℝ) ^ 3 := by ring
    let slope : ℝ :=
      1 - (x ^ 2 + x * c + c ^ 2) / 6 -
        5 * (x ^ 3 + x ^ 2 * c + x * c ^ 2 + c ^ 3) / 96
    have hslopePositive : 0 < slope := by
      dsimp [slope]
      have hcSquared : c ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by
        gcongr
      have hcCubed : c ^ 3 ≤ (2 / 3 : ℝ) ^ 3 := by
        gcongr
      nlinarith
    have hfactorization :
        (x - x ^ 3 / 6 - 1 / 2 - 5 * x ^ 4 / 96) -
            (c - c ^ 3 / 6 - 1 / 2 - 5 * c ^ 4 / 96) =
          (x - c) * slope := by
      dsimp [slope]
      ring
    have hdifferenceNonnegative :
        0 ≤
          (x - x ^ 3 / 6 - 1 / 2 - 5 * x ^ 4 / 96) -
            (c - c ^ 3 / 6 - 1 / 2 - 5 * c ^ 4 / 96) := by
      rw [hfactorization]
      exact
        mul_nonneg
          (by dsimp [c]; linarith)
          hslopePositive.le
    have hcPositive :
        0 < c - c ^ 3 / 6 - 1 / 2 - 5 * c ^ 4 / 96 := by
      norm_num [c]
    nlinarith
  have hamplitudeLower : (63 / 20 : ℝ) < 10 / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    nlinarith
  have hamplitudeUpper : 10 / Real.pi < (13 / 4 : ℝ) := by
    apply (div_lt_iff₀ Real.pi_pos).2
    nlinarith
  refine ⟨hamplitude, ?_, ?_⟩
  · rw [hamplitude]
    change |10 / Real.pi - 16 / 5| < 1 / 20
    rw [abs_lt]
    constructor <;> linarith
  · intro choice
    rw [hamplitude]
    cases choice with
    | D =>
        rfl
    | A =>
        change |10 / Real.pi - 16 / 5| ≤ |10 / Real.pi - 2|
        apply (sq_le_sq).mp
        nlinarith
    | B =>
        change |10 / Real.pi - 16 / 5| ≤ |10 / Real.pi - 12 / 5|
        apply (sq_le_sq).mp
        nlinarith
    | C =>
        change |10 / Real.pi - 16 / 5| ≤ |10 / Real.pi - 14 / 5|
        apply (sq_le_sq).mp
        nlinarith

end PhyXMiniProblems.ProblemPhyXMini0305
