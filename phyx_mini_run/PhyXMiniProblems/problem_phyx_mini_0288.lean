import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0288

open Dimension

/-!
# Phase of a sinusoidal string wave from a transverse-velocity graph

The source wave is
`y(x,t) = y_m sin (k x - omega t + phi)`. The supplied figure plots the
transverse velocity of the string point `x = 0` against time. Its vertical
axis is in metres per second, the labelled scale is `u_s = 4 m/s`, the curve
has extrema `+5 m/s` and `-5 m/s`, and at `t = 0` the curve is at `-u_s`
and rising.

Physlib dimensionful quantities below represent lengths, wave number,
angular frequency, velocity, and acceleration independently of a choice of
units. Real numbers are used only for coherent unit readouts, coordinates in
named units, and dimensionless radian representatives of angles.
-/

/-- Velocity has physical dimension length divided by time. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- Acceleration has physical dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative displacement amplitude. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed coordinate or transverse displacement on the one-dimensional string. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative wave-number magnitude, carrying inverse-length dimension. -/
abbrev WaveNumberMagnitude : Type := Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A nonnegative angular-frequency magnitude, carrying inverse-time dimension. -/
abbrev AngularFrequencyMagnitude : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative transverse-speed magnitude. -/
abbrev SpeedMagnitude : Type :=
  Dimensionful (WithDim velocityDimension NNReal)

/-- A signed transverse-velocity component. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A signed transverse-acceleration component. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- Read a nonnegative length in a selected length unit. -/
def lengthMagnitudeReadout
    (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed length in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (length : SignedLengthQuantity) : ℝ :=
  (length {UnitChoices.SI with length := unit}).val

/-- Read wave number in inverse units of a selected length unit. -/
def waveNumberReadout
    (unit : LengthUnit) (waveNumber : WaveNumberMagnitude) : ℝ :=
  ((waveNumber {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read angular frequency in inverse units of a selected time unit. -/
def angularFrequencyReadout
    (unit : TimeUnit) (frequency : AngularFrequencyMagnitude) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a nonnegative speed in coherent selected units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedMagnitude) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a signed velocity in coherent selected units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a signed acceleration in coherent selected units. -/
def signedAccelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  (acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a signed position or displacement in metres. -/
def lengthInMeters (length : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters length

/-- Read wave number in radians per metre. -/
def waveNumberInRadiansPerMeter (waveNumber : WaveNumberMagnitude) : ℝ :=
  waveNumberReadout LengthUnit.meters waveNumber

/-- Read angular frequency in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyMagnitude) : ℝ :=
  angularFrequencyReadout TimeUnit.seconds frequency

/-- Read a nonnegative speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedMagnitude) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Read a signed transverse velocity in metres per second. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Read a signed transverse acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  signedAccelerationReadout
    LengthUnit.meters TimeUnit.seconds acceleration

/-- The literal symbols printed beside the graph axes. -/
inductive GraphAxisSymbol where
  | t
  | u
  deriving DecidableEq, Repr

/-- Named velocity levels and the time origin visible in the supplied graph. -/
inductive VelocityGraphLabel where
  | positivePeak
  | positiveScale
  | timeOrigin
  | negativeScale
  | negativeTrough
  deriving DecidableEq, Repr

/-- The transverse-velocity-versus-time figure and its dimensionful labels. -/
structure TransverseVelocityTimeFigure where
  horizontalAxisSymbol : GraphAxisSymbol
  verticalAxisSymbol : GraphAxisSymbol
  velocityLengthUnit : LengthUnit
  velocityTimeUnit : TimeUnit
  observationPosition : SignedLengthQuantity
  velocityScale : SpeedMagnitude
  markedVelocity : VelocityGraphLabel → SignedVelocityQuantity

/-!
The physical wave setup. Time arguments are real coordinates measured in
seconds. The position argument and all response values remain dimensionful.
The phase is an angle modulo `2*pi`; `Real.Angle.toReal` supplies its canonical
representative in `(-pi, pi]`.
-/
structure SinusoidalStringWaveSetup where
  displacementAmplitude : LengthMagnitude
  waveNumber : WaveNumberMagnitude
  angularFrequency : AngularFrequencyMagnitude
  phase : Real.Angle
  displacementAtSeconds :
    SignedLengthQuantity → ℝ → SignedLengthQuantity
  transverseVelocityAtSeconds :
    SignedLengthQuantity → ℝ → SignedVelocityQuantity
  transverseAccelerationAtSeconds :
    SignedLengthQuantity → ℝ → SignedAccelerationQuantity
  maximumTransverseSpeed : SpeedMagnitude
  figure : TransverseVelocityTimeFigure

/-!
Data read directly from the problem statement and primary image. The evenly
spaced horizontal grid makes the unlabeled extrema `+5 m/s` and `-5 m/s`:
the `u_s = 4 m/s` line is one grid interval below the positive peak. At the
vertical time axis the curve is at `-u_s` and has positive slope.

No field specifies the phase or selects an answer choice.
-/
structure MatchesTransverseVelocityGraph
    (setup : SinusoidalStringWaveSetup) : Prop where
  horizontalAxisIsTime : setup.figure.horizontalAxisSymbol = .t
  verticalAxisIsTransverseVelocity : setup.figure.verticalAxisSymbol = .u
  velocityUsesMeters :
    setup.figure.velocityLengthUnit = LengthUnit.meters
  velocityUsesSeconds :
    setup.figure.velocityTimeUnit = TimeUnit.seconds
  observationPointIsXZero :
    lengthInMeters setup.figure.observationPosition = 0
  scaleReadout :
    speedInMetersPerSecond setup.figure.velocityScale = 4
  positiveScaleReadout :
    velocityInMetersPerSecond
        (setup.figure.markedVelocity .positiveScale) = 4
  negativeScaleReadout :
    velocityInMetersPerSecond
        (setup.figure.markedVelocity .negativeScale) = -4
  originVelocityIsNegativeScale :
    setup.figure.markedVelocity .timeOrigin =
      setup.figure.markedVelocity .negativeScale
  velocityCurveAtOrigin :
    setup.transverseVelocityAtSeconds setup.figure.observationPosition 0 =
      setup.figure.markedVelocity .timeOrigin
  positivePeakReadout :
    velocityInMetersPerSecond
        (setup.figure.markedVelocity .positivePeak) = 5
  positivePeakOccursOnCurve :
    ∃ timeInSeconds : ℝ,
      setup.transverseVelocityAtSeconds setup.figure.observationPosition
          timeInSeconds = setup.figure.markedVelocity .positivePeak
  positivePeakIsMaximum :
    velocityInMetersPerSecond
        (setup.figure.markedVelocity .positivePeak) =
      speedInMetersPerSecond setup.maximumTransverseSpeed
  negativeTroughReadout :
    velocityInMetersPerSecond
        (setup.figure.markedVelocity .negativeTrough) = -5
  negativeTroughOccursOnCurve :
    ∃ timeInSeconds : ℝ,
      setup.transverseVelocityAtSeconds setup.figure.observationPosition
          timeInSeconds = setup.figure.markedVelocity .negativeTrough
  curveRisingAtOrigin :
    0 < accelerationInMetersPerSecondSquared
      (setup.transverseAccelerationAtSeconds
        setup.figure.observationPosition 0)

/-!
The governing laws for the stated traveling-wave convention
`y(x,t) = y_m sin (k*x - omega*t + phi)`.

The derivative fields express transverse velocity as `dy/dt` and transverse
acceleration as `du/dt`. The last two fields give the physical meaning of the
maximum transverse speed. None of these laws states the requested numerical
phase.
-/
structure SatisfiesSinusoidalTravelingWave
    (setup : SinusoidalStringWaveSetup) : Prop where
  displacementAmplitudePositive :
    0 < lengthMagnitudeReadout LengthUnit.meters
      setup.displacementAmplitude
  waveNumberPositive :
    0 < waveNumberInRadiansPerMeter setup.waveNumber
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  displacementNormalForm :
    ∀ (position : SignedLengthQuantity) (timeInSeconds : ℝ)
        (displacementUnit : LengthUnit),
      signedLengthReadout displacementUnit
          (setup.displacementAtSeconds position timeInSeconds) =
        lengthMagnitudeReadout displacementUnit
            setup.displacementAmplitude *
          Real.sin
            (waveNumberInRadiansPerMeter setup.waveNumber *
                lengthInMeters position -
              angularFrequencyInRadiansPerSecond setup.angularFrequency *
                timeInSeconds +
              setup.phase.toReal)
  transverseVelocityIsTimeDerivative :
    ∀ (position : SignedLengthQuantity) (timeInSeconds : ℝ)
        (displacementUnit : LengthUnit),
      HasDerivAt
        (fun time ↦
          signedLengthReadout displacementUnit
            (setup.displacementAtSeconds position time))
        (signedVelocityReadout displacementUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position timeInSeconds))
        timeInSeconds
  transverseAccelerationIsTimeDerivative :
    ∀ (position : SignedLengthQuantity) (timeInSeconds : ℝ)
        (displacementUnit : LengthUnit),
      HasDerivAt
        (fun time ↦
          signedVelocityReadout displacementUnit TimeUnit.seconds
            (setup.transverseVelocityAtSeconds position time))
        (signedAccelerationReadout displacementUnit TimeUnit.seconds
          (setup.transverseAccelerationAtSeconds position timeInSeconds))
        timeInSeconds
  maximumSpeedBoundsVelocity :
    ∀ (position : SignedLengthQuantity) (timeInSeconds : ℝ)
        (displacementUnit : LengthUnit),
      |signedVelocityReadout displacementUnit TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position timeInSeconds)| ≤
        speedReadout displacementUnit TimeUnit.seconds
          setup.maximumTransverseSpeed
  maximumSpeedIsAttained :
    ∀ (position : SignedLengthQuantity) (displacementUnit : LengthUnit),
      ∃ timeInSeconds : ℝ,
        |signedVelocityReadout displacementUnit TimeUnit.seconds
            (setup.transverseVelocityAtSeconds position timeInSeconds)| =
          speedReadout displacementUnit TimeUnit.seconds
            setup.maximumTransverseSpeed

/-!
Differentiating the source's displacement normal form gives
`u(x,t) = -omega*y_m*cos(k*x - omega*t + phi)` in coherent units. This is a
derived law, not a premise field.
-/
lemma transverse_velocity_normal_form
    (setup : SinusoidalStringWaveSetup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup)
    (position : SignedLengthQuantity) (timeInSeconds : ℝ)
    (displacementUnit : LengthUnit) :
    signedVelocityReadout displacementUnit TimeUnit.seconds
        (setup.transverseVelocityAtSeconds position timeInSeconds) =
      -(angularFrequencyInRadiansPerSecond setup.angularFrequency *
          lengthMagnitudeReadout displacementUnit
            setup.displacementAmplitude) *
        Real.cos
          (waveNumberInRadiansPerMeter setup.waveNumber *
              lengthInMeters position -
            angularFrequencyInRadiansPerSecond setup.angularFrequency *
              timeInSeconds +
            setup.phase.toReal) := by
  let amplitude :=
    lengthMagnitudeReadout displacementUnit setup.displacementAmplitude
  let waveNumber := waveNumberInRadiansPerMeter setup.waveNumber
  let omega :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let positionInMeters := lengthInMeters position
  let phase := setup.phase.toReal
  have hArgument :
      HasDerivAt
        (fun time : ℝ =>
          waveNumber * positionInMeters - omega * time + phase)
        (-omega) timeInSeconds := by
    simpa only [id_eq, Pi.sub_apply, zero_sub, mul_one] using
      ((hasDerivAt_const timeInSeconds
          (waveNumber * positionInMeters)).sub
        ((hasDerivAt_id timeInSeconds).const_mul omega)).add_const phase
  have hNormalFormDerivative :
      HasDerivAt
        (fun time : ℝ =>
          amplitude *
            Real.sin
              (waveNumber * positionInMeters - omega * time + phase))
        (amplitude *
          (Real.cos
            (waveNumber * positionInMeters -
              omega * timeInSeconds + phase) * -omega))
        timeInSeconds := by
    exact hArgument.sin.const_mul amplitude
  have hDisplacementDerivative :
      HasDerivAt
        (fun time : ℝ =>
          signedLengthReadout displacementUnit
            (setup.displacementAtSeconds position time))
        (amplitude *
          (Real.cos
            (waveNumber * positionInMeters -
              omega * timeInSeconds + phase) * -omega))
        timeInSeconds :=
    hNormalFormDerivative.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun time =>
        hLaws.displacementNormalForm position time displacementUnit))
  simpa only [neg_mul, mul_neg, mul_assoc, mul_left_comm, mul_comm] using
    (hLaws.transverseVelocityIsTimeDerivative
      position timeInSeconds displacementUnit).unique
      hDisplacementDerivative

/-- The velocity amplitude of the sinusoidal wave is `omega*y_m`. -/
lemma maximum_transverse_speed_eq_angularFrequency_mul_amplitude
    (setup : SinusoidalStringWaveSetup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup)
    (displacementUnit : LengthUnit) :
    speedReadout displacementUnit TimeUnit.seconds
        setup.maximumTransverseSpeed =
      angularFrequencyInRadiansPerSecond setup.angularFrequency *
        lengthMagnitudeReadout displacementUnit
          setup.displacementAmplitude := by
  let omega :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let amplitude :=
    lengthMagnitudeReadout displacementUnit setup.displacementAmplitude
  let maximumSpeed :=
    speedReadout displacementUnit TimeUnit.seconds
      setup.maximumTransverseSpeed
  have hOmegaPositive : 0 < omega := by
    dsimp only [omega]
    exact hLaws.angularFrequencyPositive
  have hAmplitudeNonnegative : 0 ≤ amplitude := by
    dsimp only [amplitude, lengthMagnitudeReadout]
    positivity
  have hProductNonnegative : 0 ≤ omega * amplitude :=
    mul_nonneg hOmegaPositive.le hAmplitudeNonnegative
  have hMaximum_le_product : maximumSpeed ≤ omega * amplitude := by
    obtain ⟨time, hAttained⟩ :=
      hLaws.maximumSpeedIsAttained
        setup.figure.observationPosition displacementUnit
    have hVelocity :=
      transverse_velocity_normal_form setup hLaws
        setup.figure.observationPosition time displacementUnit
    rw [hVelocity] at hAttained
    calc
      maximumSpeed =
          |-(omega * amplitude) *
            Real.cos
              (waveNumberInRadiansPerMeter setup.waveNumber *
                  lengthInMeters setup.figure.observationPosition -
                omega * time + setup.phase.toReal)| := by
            exact hAttained.symm
      _ = (omega * amplitude) *
          |Real.cos
            (waveNumberInRadiansPerMeter setup.waveNumber *
                lengthInMeters setup.figure.observationPosition -
              omega * time + setup.phase.toReal)| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hProductNonnegative]
      _ ≤ (omega * amplitude) * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one _) hProductNonnegative
      _ = omega * amplitude := by ring
  have hProduct_le_maximum : omega * amplitude ≤ maximumSpeed := by
    let position := setup.figure.observationPosition
    let phaseArgument :=
      waveNumberInRadiansPerMeter setup.waveNumber *
          lengthInMeters position +
        setup.phase.toReal
    let time := phaseArgument / omega
    have hPhaseAtTime :
        waveNumberInRadiansPerMeter setup.waveNumber *
              lengthInMeters position -
            omega * time + setup.phase.toReal = 0 := by
      dsimp only [time, phaseArgument]
      field_simp [ne_of_gt hOmegaPositive]
      ring
    have hBound :=
      hLaws.maximumSpeedBoundsVelocity position time displacementUnit
    have hVelocity :=
      transverse_velocity_normal_form setup hLaws
        position time displacementUnit
    rw [hVelocity, hPhaseAtTime, Real.cos_zero, mul_one,
      abs_neg, abs_of_nonneg hProductNonnegative] at hBound
    exact hBound
  exact le_antisymm hMaximum_le_product hProduct_le_maximum

/-!
At `x = 0`, `t = 0`, the graph gives `u/u_max = -4/5`. The derived velocity
law therefore gives `cos(phi) = 4/5`. The graph is rising there, so its
acceleration is positive; differentiating once more puts the canonical phase
in quadrant IV. Thus its exact principal representative is
`-arccos (4/5)`.
-/
lemma phase_from_transverse_velocity_graph
    (setup : SinusoidalStringWaveSetup)
    (hData : MatchesTransverseVelocityGraph setup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup) :
    setup.phase.toReal = -Real.arccos ((4 : ℝ) / 5) := by
  let position := setup.figure.observationPosition
  let omega :=
    angularFrequencyInRadiansPerSecond setup.angularFrequency
  let amplitude :=
    lengthMagnitudeReadout LengthUnit.meters setup.displacementAmplitude
  let waveNumber := waveNumberInRadiansPerMeter setup.waveNumber
  let positionInMeters := lengthInMeters position
  let phase := setup.phase.toReal
  have hOmegaPositive : 0 < omega := by
    dsimp only [omega]
    exact hLaws.angularFrequencyPositive
  have hPositionZero : positionInMeters = 0 := by
    dsimp only [positionInMeters, position]
    exact hData.observationPointIsXZero
  have hVelocityAtOrigin :
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position 0) = -4 := by
    change velocityInMetersPerSecond
        (setup.transverseVelocityAtSeconds position 0) = -4
    rw [hData.velocityCurveAtOrigin]
    rw [hData.originVelocityIsNegativeScale]
    exact hData.negativeScaleReadout
  have hMaximumSpeedFive :
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.maximumTransverseSpeed = 5 := by
    change speedInMetersPerSecond setup.maximumTransverseSpeed = 5
    rw [← hData.positivePeakIsMaximum]
    exact hData.positivePeakReadout
  have hVelocityAmplitudeFive : omega * amplitude = 5 := by
    have hMaximumFormula :=
      maximum_transverse_speed_eq_angularFrequency_mul_amplitude
        setup hLaws LengthUnit.meters
    change
      speedReadout LengthUnit.meters TimeUnit.seconds
          setup.maximumTransverseSpeed =
        omega * amplitude at hMaximumFormula
    linarith
  have hCosinePhase : Real.cos phase = (4 : ℝ) / 5 := by
    have hVelocityFormula :=
      transverse_velocity_normal_form setup hLaws
        position 0 LengthUnit.meters
    change
      signedVelocityReadout LengthUnit.meters TimeUnit.seconds
          (setup.transverseVelocityAtSeconds position 0) =
        -(omega * amplitude) *
          Real.cos
            (waveNumber * positionInMeters - omega * 0 + phase)
      at hVelocityFormula
    rw [hPositionZero, hVelocityAmplitudeFive] at hVelocityFormula
    norm_num at hVelocityFormula
    linarith
  have hArgumentDerivative :
      HasDerivAt
        (fun time : ℝ =>
          waveNumber * positionInMeters - omega * time + phase)
        (-omega) 0 := by
    simpa only [id_eq, Pi.sub_apply, zero_sub, mul_one] using
      ((hasDerivAt_const (0 : ℝ)
          (waveNumber * positionInMeters)).sub
        ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul omega)).add_const phase
  have hVelocityFormulaDerivative :
      HasDerivAt
        (fun time : ℝ =>
          -(omega * amplitude) *
            Real.cos
              (waveNumber * positionInMeters - omega * time + phase))
        (-(omega * amplitude) *
          (-Real.sin
            (waveNumber * positionInMeters - omega * 0 + phase) *
              -omega))
        0 := by
    exact hArgumentDerivative.cos.const_mul (-(omega * amplitude))
  have hVelocityDerivative :
      HasDerivAt
        (fun time : ℝ =>
          signedVelocityReadout LengthUnit.meters TimeUnit.seconds
            (setup.transverseVelocityAtSeconds position time))
        (-(omega * amplitude) *
          (-Real.sin
            (waveNumber * positionInMeters - omega * 0 + phase) *
              -omega))
        0 :=
    hVelocityFormulaDerivative.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun time => by
        exact transverse_velocity_normal_form setup hLaws
          position time LengthUnit.meters))
  have hAccelerationFormula :
      signedAccelerationReadout LengthUnit.meters TimeUnit.seconds
          (setup.transverseAccelerationAtSeconds position 0) =
        -(omega * amplitude) *
          (-Real.sin
            (waveNumber * positionInMeters - omega * 0 + phase) *
              -omega) :=
    (hLaws.transverseAccelerationIsTimeDerivative
      position 0 LengthUnit.meters).unique hVelocityDerivative
  have hAccelerationPositive :
      0 <
        signedAccelerationReadout LengthUnit.meters TimeUnit.seconds
          (setup.transverseAccelerationAtSeconds position 0) := by
    change
      0 < accelerationInMetersPerSecondSquared
        (setup.transverseAccelerationAtSeconds position 0)
    exact hData.curveRisingAtOrigin
  have hSinePhaseNegative : Real.sin phase < 0 := by
    rw [hPositionZero, hVelocityAmplitudeFive] at hAccelerationFormula
    norm_num at hAccelerationFormula
    nlinarith
  have hPhaseRange := setup.phase.toReal_mem_Ioc
  have hPhaseNegative : phase < 0 := by
    by_contra hNotNegative
    have hPhaseNonnegative : 0 ≤ phase := le_of_not_gt hNotNegative
    have hSineNonnegative : 0 ≤ Real.sin phase :=
      Real.sin_nonneg_of_nonneg_of_le_pi hPhaseNonnegative hPhaseRange.2
    linarith
  have hArccos :
      Real.arccos ((4 : ℝ) / 5) = -phase := by
    apply Real.arccos_eq_of_eq_cos
    · linarith
    · linarith [hPhaseRange.1]
    · rw [Real.cos_neg]
      exact hCosinePhase.symm
  dsimp only [phase] at hArccos ⊢
  linarith

/-- The four phase readouts printed as answer choices, in radians. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical radian readout printed beside each answer label. -/
def displayedPhaseRadians : AnswerChoice → ℝ
  | .A => -0.78
  | .B => -0.36
  | .C => 0.64
  | .D => -0.64

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A choice is at least as close as every displayed phase readout. -/
def IsNearestDisplayedPhase
    (phase : Real.Angle) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |phase.toReal - displayedPhaseRadians choice| ≤
      |phase.toReal - displayedPhaseRadians other|

/-!
The exact principal phase is `-arccos (4/5)`, approximately `-0.6435 rad`.
Consequently the nearest displayed value is choice D, `-0.64 rad`.

This formalizes `thm:physics:phyx_mini_0288:target`.
-/
theorem problem_phyx_mini_0288
    (setup : SinusoidalStringWaveSetup)
    (hData : MatchesTransverseVelocityGraph setup)
    (hLaws : SatisfiesSinusoidalTravelingWave setup) :
    setup.phase.toReal = -Real.arccos ((4 : ℝ) / 5) ∧
      IsNearestDisplayedPhase setup.phase recordedDatasetAnswer := by
  let alpha := Real.arccos ((4 : ℝ) / 5)
  have hPhase : setup.phase.toReal = -alpha := by
    dsimp only [alpha]
    exact phase_from_transverse_velocity_graph setup hData hLaws
  refine ⟨hPhase, ?_⟩
  have hAlphaNonnegative : 0 ≤ alpha := by
    dsimp only [alpha]
    exact Real.arccos_nonneg _
  have hAlphaLePi : alpha ≤ Real.pi := by
    dsimp only [alpha]
    exact Real.arccos_le_pi _
  have hCosAlpha : Real.cos alpha = (4 : ℝ) / 5 := by
    dsimp only [alpha]
    exact Real.cos_arccos (by norm_num) (by norm_num)
  have hCosHalf : (4 : ℝ) / 5 < Real.cos ((1 : ℝ) / 2) := by
    have hTaylor :=
      Real.one_sub_sq_div_two_le_cos (x := (1 : ℝ) / 2)
    norm_num at hTaylor ⊢
    linarith
  have hHalfLeAlpha : (1 : ℝ) / 2 ≤ alpha := by
    by_contra hNot
    have hAlphaLtHalf : alpha < (1 : ℝ) / 2 := lt_of_not_ge hNot
    have hHalfLePi : (1 : ℝ) / 2 ≤ Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hCosOrder :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        hAlphaNonnegative hHalfLePi hAlphaLtHalf
    rw [hCosAlpha] at hCosOrder
    linarith
  have hCosSeventyOne :
      Real.cos ((71 : ℝ) / 100) < (4 : ℝ) / 5 := by
    have hTaylor :=
      Real.cos_bound (x := (71 : ℝ) / 100) (by norm_num)
    have hUpper := (abs_le.mp hTaylor).2
    norm_num [abs_of_nonneg] at hUpper ⊢
    linarith
  have hAlphaLeSeventyOne : alpha ≤ (71 : ℝ) / 100 := by
    by_contra hNot
    have hSeventyOneLtAlpha : (71 : ℝ) / 100 < alpha :=
      lt_of_not_ge hNot
    have hCosOrder :=
      Real.cos_lt_cos_of_nonneg_of_le_pi
        (by norm_num : (0 : ℝ) ≤ 71 / 100)
        hAlphaLePi hSeventyOneLtAlpha
    rw [hCosAlpha] at hCosOrder
    linarith
  unfold IsNearestDisplayedPhase
  intro other
  rw [hPhase]
  cases other with
  | A =>
      simp only [recordedDatasetAnswer, displayedPhaseRadians]
      rw [← sq_le_sq]
      nlinarith
  | B =>
      simp only [recordedDatasetAnswer, displayedPhaseRadians]
      rw [← sq_le_sq]
      nlinarith
  | C =>
      simp only [recordedDatasetAnswer, displayedPhaseRadians]
      rw [← sq_le_sq]
      nlinarith
  | D =>
      rfl

end PhyXMiniProblems.ProblemPhyXMini0288
