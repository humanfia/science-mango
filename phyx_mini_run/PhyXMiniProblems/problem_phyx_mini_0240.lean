import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0240

open Dimension

/-!
# Maximum transverse acceleration in a traveling string wave

A string is driven sinusoidally at `5.00 Hz` with amplitude `12.0 cm`.
The wave travels to the right at `20.0 m/s`.  The primary figure marks the
amplitude `A` from the dashed equilibrium line to a crest, labels the
rightward propagation velocity by `v⃗`, and shows the left end attached to a
wall.

Physical quantities below use Physlib's unit-independent `Dimensionful`
types.  Real numbers occur only as explicitly named scalar readouts,
dimensionless phases, and displayed multiple-choice values.
-/

/-! ## Dimensionful physical quantities and named SI readouts -/

/-- A nonnegative physical transverse amplitude. -/
abbrev AmplitudeQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical axial position or transverse displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A signed physical time coordinate relative to a chosen origin. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 ℝ)

/-- An ordinary cyclic frequency, whose SI readout is in hertz. -/
abbrev CyclicFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- An angular frequency, whose SI readout is in radians per second. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A wave number, whose SI readout is in radians per meter. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A signed transverse acceleration component. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a nonnegative amplitude in meters. -/
def amplitudeInMeters (amplitude : AmplitudeQuantity) : ℝ :=
  ((amplitude UnitChoices.SI).val : ℝ)

/-- Read a nonnegative amplitude in centimeters. -/
def amplitudeInCentimeters (amplitude : AmplitudeQuantity) : ℝ :=
  ((amplitude
    {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Read a signed axial position or displacement in meters. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a time coordinate in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Read an ordinary cyclic frequency in hertz. -/
def frequencyInHertz (frequency : CyclicFrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read an angular frequency in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : AngularFrequencyQuantity) : ℝ :=
  ((angularFrequency UnitChoices.SI).val : ℝ)

/-- Read a wave number in radians per meter. -/
def waveNumberInRadiansPerMeter (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-- Read a propagation speed in meters per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read a signed transverse acceleration in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-! ## Physical and primary-figure roles -/

/-- The disturbance carried by the string. -/
inductive StringWaveKind where
  | transverseSinusoidal
  deriving DecidableEq, Repr

/-- Direction of travel along the string's axial coordinate. -/
inductive PropagationDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Mechanical attachment shown at the left end of the string. -/
inductive StringAttachment where
  | fixedWall
  | free
  deriving DecidableEq, Repr

/-- Text labels visible in the primary figure. -/
inductive StringWaveFigureLabel where
  | amplitudeA
  | propagationVelocity
  deriving DecidableEq, Repr

/-- Geometric features to which the figure labels point. -/
inductive StringWaveFigureFeature where
  | verticalEquilibriumToCrestArrow
  | rightwardPropagationArrow
  deriving DecidableEq, Repr

/-!
The independent physical quantities, figure roles, and time-dependent fields
of the modeled string wave.  The displacement and acceleration remain
independent fields until the governing-law premise is supplied.
-/
structure TravelingStringWaveSetup where
  waveKind : StringWaveKind
  propagationDirection : PropagationDirection
  leftAttachment : StringAttachment
  showsDashedEquilibriumLine : Bool
  figureLabelTarget : StringWaveFigureLabel → StringWaveFigureFeature
  amplitude : AmplitudeQuantity
  cyclicDrivingFrequency : CyclicFrequencyQuantity
  angularFrequency : AngularFrequencyQuantity
  waveSpeed : SpeedQuantity
  waveNumber : WaveNumberQuantity
  axialOrigin : SignedLengthQuantity
  timeOrigin : TimeQuantity
  phaseOffsetRadians : ℝ
  transverseDisplacement :
    SignedLengthQuantity → TimeQuantity → SignedLengthQuantity
  transverseAcceleration :
    SignedLengthQuantity → TimeQuantity → AccelerationQuantity

/-!
Qualitative information read from the primary figure.  In particular, the
`A` arrow measures crest height from equilibrium and the velocity arrow
points right.  This predicate contains no acceleration value.
-/
structure MatchesPrimaryStringWaveFigure
    (setup : TravelingStringWaveSetup) : Prop where
  waveIsTransverseAndSinusoidal :
    setup.waveKind = .transverseSinusoidal
  propagationIsRightward :
    setup.propagationDirection = .right
  leftEndIsAttachedToWall :
    setup.leftAttachment = .fixedWall
  dashedLineMarksEquilibrium :
    setup.showsDashedEquilibriumLine = true
  amplitudeLabelTargetsCrestHeight :
    setup.figureLabelTarget .amplitudeA =
      .verticalEquilibriumToCrestArrow
  velocityLabelTargetsRightwardArrow :
    setup.figureLabelTarget .propagationVelocity =
      .rightwardPropagationArrow

/-!
Numerical and origin data stated in the problem.  The final field is the
given condition `y = 0` at `x = 0` and `t = 0`, not a maximum-acceleration
condition.
-/
structure HasStringWaveProblemData
    (setup : TravelingStringWaveSetup) : Prop where
  drivingFrequencyHertz :
    frequencyInHertz setup.cyclicDrivingFrequency = 5
  amplitudeCentimeters :
    amplitudeInCentimeters setup.amplitude = 12
  waveSpeedMetersPerSecond :
    speedInMetersPerSecond setup.waveSpeed = 20
  axialOriginMeters :
    signedLengthInMeters setup.axialOrigin = 0
  timeOriginSeconds :
    timeInSeconds setup.timeOrigin = 0
  displacementAtSpaceTimeOrigin :
    signedLengthInMeters
      (setup.transverseDisplacement setup.axialOrigin setup.timeOrigin) = 0

/-- Positivity and nondegeneracy of the physical wave parameters. -/
structure HasPhysicalStringWaveParameters
    (setup : TravelingStringWaveSetup) : Prop where
  amplitudePositive :
    0 < amplitudeInMeters setup.amplitude
  cyclicFrequencyPositive :
    0 < frequencyInHertz setup.cyclicDrivingFrequency
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  waveSpeedPositive :
    0 < speedInMetersPerSecond setup.waveSpeed
  waveNumberPositive :
    0 < waveNumberInRadiansPerMeter setup.waveNumber

/-!
Generic governing laws for a right-moving sinusoidal string wave:

* `ω = 2πf`;
* the nondispersive relation `ω = v k`;
* `y(x,t) = A sin(k(x-x₀) - ω(t-t₀) + φ)`;
* each string element undergoes transverse SHM, `a_y = -ω² y`.

These pointwise laws do not state a maximum or select any answer choice.
-/
structure SatisfiesTravelingStringWaveLaws
    (setup : TravelingStringWaveSetup) : Prop where
  angularFrequencyConversion :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      2 * Real.pi * frequencyInHertz setup.cyclicDrivingFrequency
  nondispersiveWaveRelation :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      speedInMetersPerSecond setup.waveSpeed *
        waveNumberInRadiansPerMeter setup.waveNumber
  rightMovingSinusoidalDisplacement :
    ∀ (position : SignedLengthQuantity) (time : TimeQuantity),
      signedLengthInMeters (setup.transverseDisplacement position time) =
        amplitudeInMeters setup.amplitude *
          Real.sin
            (waveNumberInRadiansPerMeter setup.waveNumber *
                (signedLengthInMeters position -
                  signedLengthInMeters setup.axialOrigin) -
              angularFrequencyInRadiansPerSecond setup.angularFrequency *
                (timeInSeconds time - timeInSeconds setup.timeOrigin) +
              setup.phaseOffsetRadians)
  transverseSimpleHarmonicAcceleration :
    ∀ (position : SignedLengthQuantity) (time : TimeQuantity),
      accelerationInMetersPerSecondSquared
          (setup.transverseAcceleration position time) =
        -(angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2 *
          signedLengthInMeters (setup.transverseDisplacement position time)

/-!
A state of an element on the modeled string.  The axial coordinate is at or
to the right of the wall attachment; time is unrestricted.
-/
def StringElementState (setup : TravelingStringWaveSetup) : Type :=
  {state : SignedLengthQuantity × TimeQuantity //
    signedLengthInMeters setup.axialOrigin ≤
      signedLengthInMeters state.1}

/-- The set of all attained magnitudes of transverse acceleration, in SI. -/
def transverseAccelerationMagnitudeRange
    (setup : TravelingStringWaveSetup) : Set ℝ :=
  Set.range fun state : StringElementState setup =>
    |accelerationInMetersPerSecondSquared
      (setup.transverseAcceleration state.val.1 state.val.2)|

/-! ## Displayed choices and derived conclusions -/

/-- Labels of the four acceleration choices printed with the problem. -/
inductive AccelerationAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/--
The displayed answer values, interpreted as meter-per-second-squared
readouts because the requested quantity is transverse acceleration.
-/
def displayedAccelerationInMetersPerSecondSquared :
    AccelerationAnswerChoice → ℝ
  | .A => 128
  | .B => 113
  | .C => 108
  | .D => 118

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AccelerationAnswerChoice := .D

/-- The stated frequency gives angular frequency `ω = 10π rad/s`. -/
lemma angularFrequencyInRadiansPerSecond_eq_ten_pi
    (setup : TravelingStringWaveSetup)
    (_data : HasStringWaveProblemData setup)
    (_laws : SatisfiesTravelingStringWaveLaws setup) :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      10 * Real.pi := by
  calc
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
        2 * Real.pi * frequencyInHertz setup.cyclicDrivingFrequency :=
      _laws.angularFrequencyConversion
    _ = 10 * Real.pi := by
      rw [_data.drivingFrequencyHertz]
      ring

/-!
The supplied `20 m/s` speed and `5 Hz` drive imply the intermediate
wave-number readout `k = π/2 rad/m`.  This records the role of the given
propagation speed even though the transverse-acceleration maximum is
independent of it.
-/
lemma waveNumberInRadiansPerMeter_eq_pi_over_two
    (setup : TravelingStringWaveSetup)
    (_data : HasStringWaveProblemData setup)
    (_laws : SatisfiesTravelingStringWaveLaws setup) :
    waveNumberInRadiansPerMeter setup.waveNumber =
      Real.pi / 2 := by
  have hAngular :=
    angularFrequencyInRadiansPerSecond_eq_ten_pi setup _data _laws
  have hWaveRelation := _laws.nondispersiveWaveRelation
  rw [hAngular, _data.waveSpeedMetersPerSecond] at hWaveRelation
  linarith

/-!
The attained transverse-acceleration magnitudes have greatest element
`Aω²`.  With `A = 0.120 m` and `f = 5.00 Hz`, this is exactly
`12π² m/s²`, lies within `0.5 m/s²` of the displayed value `118`, and
choice D is closest among the four choices.

This formalizes `thm:physics:phyx_mini_0240:target`.
-/
theorem maximumTransverseAcceleration
    (setup : TravelingStringWaveSetup)
    (_figure : MatchesPrimaryStringWaveFigure setup)
    (_data : HasStringWaveProblemData setup)
    (_physical : HasPhysicalStringWaveParameters setup)
    (_laws : SatisfiesTravelingStringWaveLaws setup) :
    IsGreatest
        (transverseAccelerationMagnitudeRange setup)
        (amplitudeInMeters setup.amplitude *
          (angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2) ∧
      amplitudeInMeters setup.amplitude *
          (angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2 =
        12 * Real.pi ^ 2 ∧
      |12 * Real.pi ^ 2 -
          displayedAccelerationInMetersPerSecondSquared .D| < 1 / 2 ∧
      ∀ choice : AccelerationAnswerChoice,
        |12 * Real.pi ^ 2 -
            displayedAccelerationInMetersPerSecondSquared .D| ≤
          |12 * Real.pi ^ 2 -
            displayedAccelerationInMetersPerSecondSquared choice| := by
  have hAmplitudeConversion (amplitude : AmplitudeQuantity) :
      amplitudeInCentimeters amplitude =
        100 * amplitudeInMeters amplitude := by
    have h := congrArg (fun value : WithDim L𝓭 NNReal => (value.val : ℝ))
      (amplitude.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [amplitudeInCentimeters, amplitudeInMeters,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, WithDim.smul_val,
      NNReal.smul_def, smul_eq_mul] at h ⊢
    exact h
  have hAmplitudeMeters :
      amplitudeInMeters setup.amplitude = 3 / 25 := by
    have hConversion := hAmplitudeConversion setup.amplitude
    rw [_data.amplitudeCentimeters] at hConversion
    norm_num at hConversion ⊢
    linarith
  have hAngularFrequency :=
    angularFrequencyInRadiansPerSecond_eq_ten_pi setup _data _laws
  have hGreatest :
      IsGreatest
        (transverseAccelerationMagnitudeRange setup)
        (amplitudeInMeters setup.amplitude *
          (angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2) := by
    constructor
    · let peakTime : TimeQuantity :=
        CarriesDimension.toDimensionful UnitChoices.SI
          ⟨timeInSeconds setup.timeOrigin +
            (setup.phaseOffsetRadians - Real.pi / 2) /
              angularFrequencyInRadiansPerSecond setup.angularFrequency⟩
      have hPeakTime :
          timeInSeconds peakTime =
            timeInSeconds setup.timeOrigin +
              (setup.phaseOffsetRadians - Real.pi / 2) /
                angularFrequencyInRadiansPerSecond setup.angularFrequency := by
        simp [peakTime, timeInSeconds,
          CarriesDimension.toDimensionful_apply_apply]
      let peakState : StringElementState setup :=
        ⟨(setup.axialOrigin, peakTime), le_rfl⟩
      refine ⟨peakState, ?_⟩
      change
        |accelerationInMetersPerSecondSquared
          (setup.transverseAcceleration setup.axialOrigin peakTime)| =
            amplitudeInMeters setup.amplitude *
              (angularFrequencyInRadiansPerSecond
                setup.angularFrequency) ^ 2
      rw [_laws.transverseSimpleHarmonicAcceleration,
        _laws.rightMovingSinusoidalDisplacement]
      have hAngularFrequencyNe :
          angularFrequencyInRadiansPerSecond setup.angularFrequency ≠ 0 :=
        ne_of_gt _physical.angularFrequencyPositive
      have hPeakPhase :
          waveNumberInRadiansPerMeter setup.waveNumber *
                (signedLengthInMeters setup.axialOrigin -
                  signedLengthInMeters setup.axialOrigin) -
              angularFrequencyInRadiansPerSecond setup.angularFrequency *
                (timeInSeconds peakTime -
                  timeInSeconds setup.timeOrigin) +
              setup.phaseOffsetRadians =
            Real.pi / 2 := by
        rw [hPeakTime]
        field_simp [hAngularFrequencyNe]
        ring
      rw [hPeakPhase, Real.sin_pi_div_two]
      simp only [mul_one, abs_mul, abs_neg, abs_pow,
        abs_of_nonneg (le_of_lt _physical.angularFrequencyPositive),
        abs_of_nonneg (le_of_lt _physical.amplitudePositive)]
      ring
    · intro value hValue
      rcases hValue with ⟨state, rfl⟩
      change
        |accelerationInMetersPerSecondSquared
          (setup.transverseAcceleration state.val.1 state.val.2)| ≤
            amplitudeInMeters setup.amplitude *
              (angularFrequencyInRadiansPerSecond
                setup.angularFrequency) ^ 2
      rw [_laws.transverseSimpleHarmonicAcceleration,
        _laws.rightMovingSinusoidalDisplacement]
      let phase :=
        waveNumberInRadiansPerMeter setup.waveNumber *
              (signedLengthInMeters state.val.1 -
                signedLengthInMeters setup.axialOrigin) -
            angularFrequencyInRadiansPerSecond setup.angularFrequency *
              (timeInSeconds state.val.2 -
                timeInSeconds setup.timeOrigin) +
            setup.phaseOffsetRadians
      change
        |-(angularFrequencyInRadiansPerSecond
              setup.angularFrequency) ^ 2 *
            (amplitudeInMeters setup.amplitude * Real.sin phase)| ≤
          amplitudeInMeters setup.amplitude *
            (angularFrequencyInRadiansPerSecond
              setup.angularFrequency) ^ 2
      rw [abs_mul, abs_neg, abs_pow, abs_mul,
        abs_of_nonneg (le_of_lt _physical.angularFrequencyPositive),
        abs_of_nonneg (le_of_lt _physical.amplitudePositive)]
      calc
        (angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2 *
              (amplitudeInMeters setup.amplitude * |Real.sin phase|) =
            (amplitudeInMeters setup.amplitude *
                (angularFrequencyInRadiansPerSecond
                  setup.angularFrequency) ^ 2) * |Real.sin phase| := by
              ring
        _ ≤ (amplitudeInMeters setup.amplitude *
                (angularFrequencyInRadiansPerSecond
                  setup.angularFrequency) ^ 2) * 1 := by
              exact mul_le_mul_of_nonneg_left
                (Real.abs_sin_le_one phase)
                (mul_nonneg (le_of_lt _physical.amplitudePositive)
                  (sq_nonneg _))
        _ = amplitudeInMeters setup.amplitude *
              (angularFrequencyInRadiansPerSecond
                setup.angularFrequency) ^ 2 := by ring
  have hMaximumValue :
      amplitudeInMeters setup.amplitude *
          (angularFrequencyInRadiansPerSecond setup.angularFrequency) ^ 2 =
        12 * Real.pi ^ 2 := by
    rw [hAmplitudeMeters, hAngularFrequency]
    ring
  have hPiLower : (3.13 : ℝ) < Real.pi := by
    have hBound :=
      Real.cos_bound (x := (313 / 3200 : ℝ))
        (by norm_num [abs_of_nonneg])
    have hBase :
        (99521 / 100000 : ℝ) ≤ Real.cos (313 / 3200 : ℝ) := by
      rw [abs_le] at hBound
      norm_num at hBound ⊢
      linarith
    have hStep1 :
        Real.cos (313 / 1600 : ℝ) =
          2 * Real.cos (313 / 3200 : ℝ) ^ 2 - 1 := by
      rw [show (313 / 1600 : ℝ) = 2 * (313 / 3200) by norm_num,
        Real.cos_two_mul]
    have hBound1 :
        (98088 / 100000 : ℝ) ≤ Real.cos (313 / 1600 : ℝ) := by
      nlinarith
        [sq_nonneg
          (Real.cos (313 / 3200 : ℝ) - 99521 / 100000)]
    have hStep2 :
        Real.cos (313 / 800 : ℝ) =
          2 * Real.cos (313 / 1600 : ℝ) ^ 2 - 1 := by
      rw [show (313 / 800 : ℝ) = 2 * (313 / 1600) by norm_num,
        Real.cos_two_mul]
    have hBound2 :
        (92425 / 100000 : ℝ) ≤ Real.cos (313 / 800 : ℝ) := by
      nlinarith
        [sq_nonneg
          (Real.cos (313 / 1600 : ℝ) - 98088 / 100000)]
    have hStep3 :
        Real.cos (313 / 400 : ℝ) =
          2 * Real.cos (313 / 800 : ℝ) ^ 2 - 1 := by
      rw [show (313 / 400 : ℝ) = 2 * (313 / 800) by norm_num,
        Real.cos_two_mul]
    have hBound3 :
        (70847 / 100000 : ℝ) ≤ Real.cos (313 / 400 : ℝ) := by
      nlinarith
        [sq_nonneg
          (Real.cos (313 / 800 : ℝ) - 92425 / 100000)]
    have hStep4 :
        Real.cos (313 / 200 : ℝ) =
          2 * Real.cos (313 / 400 : ℝ) ^ 2 - 1 := by
      rw [show (313 / 200 : ℝ) = 2 * (313 / 400) by norm_num,
        Real.cos_two_mul]
    have hCosPositive : 0 < Real.cos (313 / 200 : ℝ) := by
      nlinarith
        [sq_nonneg
          (Real.cos (313 / 400 : ℝ) - 70847 / 100000)]
    by_contra hPi
    have hPiHalfLe : Real.pi / 2 ≤ (313 / 200 : ℝ) := by
      norm_num at hPi ⊢
      linarith
    have hCosNonpositive : Real.cos (313 / 200 : ℝ) ≤ 0 := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (x := Real.pi / 2) (y := (313 / 200 : ℝ)) (by positivity)
        (by nlinarith [Real.two_le_pi]) hPiHalfLe
      simpa using h
    linarith
  have hPiUpper : Real.pi < (3.142 : ℝ) := by
    have hBound :=
      Real.cos_bound (x := (1571 / 32000 : ℝ))
        (by norm_num [abs_of_nonneg])
    have hBase :
        Real.cos (1571 / 32000 : ℝ) ≤
          (9987953 / 10000000 : ℝ) := by
      rw [abs_le] at hBound
      norm_num at hBound ⊢
      linarith
    have hBaseNonnegative :
        0 ≤ Real.cos (1571 / 32000 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hStep1 :
        Real.cos (1571 / 16000 : ℝ) =
          2 * Real.cos (1571 / 32000 : ℝ) ^ 2 - 1 := by
      rw [show (1571 / 16000 : ℝ) = 2 * (1571 / 32000) by norm_num,
        Real.cos_two_mul]
    have hBound1 :
        Real.cos (1571 / 16000 : ℝ) ≤
          (9951842 / 10000000 : ℝ) := by
      nlinarith
        [sq_nonneg
          (Real.cos (1571 / 32000 : ℝ) - 9987953 / 10000000)]
    have hStep1Nonnegative :
        0 ≤ Real.cos (1571 / 16000 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hStep2 :
        Real.cos (1571 / 8000 : ℝ) =
          2 * Real.cos (1571 / 16000 : ℝ) ^ 2 - 1 := by
      rw [show (1571 / 8000 : ℝ) = 2 * (1571 / 16000) by norm_num,
        Real.cos_two_mul]
    have hBound2 :
        Real.cos (1571 / 8000 : ℝ) ≤
          (9807832 / 10000000 : ℝ) := by
      nlinarith
        [sq_nonneg
          (Real.cos (1571 / 16000 : ℝ) - 9951842 / 10000000)]
    have hStep2Nonnegative :
        0 ≤ Real.cos (1571 / 8000 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hStep3 :
        Real.cos (1571 / 4000 : ℝ) =
          2 * Real.cos (1571 / 8000 : ℝ) ^ 2 - 1 := by
      rw [show (1571 / 4000 : ℝ) = 2 * (1571 / 8000) by norm_num,
        Real.cos_two_mul]
    have hBound3 :
        Real.cos (1571 / 4000 : ℝ) ≤
          (9238714 / 10000000 : ℝ) := by
      nlinarith
        [sq_nonneg
          (Real.cos (1571 / 8000 : ℝ) - 9807832 / 10000000)]
    have hStep3Nonnegative :
        0 ≤ Real.cos (1571 / 4000 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hStep4 :
        Real.cos (1571 / 2000 : ℝ) =
          2 * Real.cos (1571 / 4000 : ℝ) ^ 2 - 1 := by
      rw [show (1571 / 2000 : ℝ) = 2 * (1571 / 4000) by norm_num,
        Real.cos_two_mul]
    have hBound4 :
        Real.cos (1571 / 2000 : ℝ) ≤
          (7070768 / 10000000 : ℝ) := by
      nlinarith
        [sq_nonneg
          (Real.cos (1571 / 4000 : ℝ) - 9238714 / 10000000)]
    have hStep4Nonnegative :
        0 ≤ Real.cos (1571 / 2000 : ℝ) :=
      (Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])).le
    have hStep5 :
        Real.cos (1571 / 1000 : ℝ) =
          2 * Real.cos (1571 / 2000 : ℝ) ^ 2 - 1 := by
      rw [show (1571 / 1000 : ℝ) = 2 * (1571 / 2000) by norm_num,
        Real.cos_two_mul]
    have hCosNegative : Real.cos (1571 / 1000 : ℝ) < 0 := by
      nlinarith
        [sq_nonneg
          (Real.cos (1571 / 2000 : ℝ) - 7070768 / 10000000)]
    by_contra hPi
    have hPiHalfGe : (1571 / 1000 : ℝ) ≤ Real.pi / 2 := by
      norm_num at hPi ⊢
      linarith
    have hCosNonnegative : 0 ≤ Real.cos (1571 / 1000 : ℝ) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by nlinarith [Real.pi_pos]) hPiHalfGe
    linarith
  have hPiSquareLower :
      (313 / 100 : ℝ) ^ 2 < Real.pi ^ 2 := by
    nlinarith
      [mul_pos (sub_pos.mpr hPiLower)
        (by nlinarith [Real.pi_pos] :
          0 < Real.pi + (313 / 100 : ℝ))]
  have hPiSquareUpper :
      Real.pi ^ 2 < (1571 / 500 : ℝ) ^ 2 := by
    nlinarith
      [mul_pos (sub_pos.mpr hPiUpper)
        (by nlinarith [Real.pi_pos] :
          0 < (1571 / 500 : ℝ) + Real.pi)]
  have hAccelerationLower : (235 / 2 : ℝ) < 12 * Real.pi ^ 2 := by
    norm_num at hPiSquareLower ⊢
    linarith only [hPiSquareLower]
  have hAccelerationUpper : 12 * Real.pi ^ 2 < (237 / 2 : ℝ) := by
    norm_num at hPiSquareUpper ⊢
    linarith only [hPiSquareUpper]
  have hNearDisplayedD :
      |12 * Real.pi ^ 2 - 118| < (1 / 2 : ℝ) :=
    abs_lt.mpr ⟨by linarith only [hAccelerationLower],
      by linarith only [hAccelerationUpper]⟩
  refine ⟨hGreatest, hMaximumValue, ?_, ?_⟩
  · simpa [displayedAccelerationInMetersPerSecondSquared] using
      hNearDisplayedD
  · intro choice
    cases choice with
    | A =>
        simp only [displayedAccelerationInMetersPerSecondSquared]
        rw [abs_of_nonpos
            (by linarith only [hAccelerationUpper] :
              12 * Real.pi ^ 2 - 128 ≤ 0)]
        linarith only [hNearDisplayedD, hAccelerationUpper]
    | B =>
        simp only [displayedAccelerationInMetersPerSecondSquared]
        rw [abs_of_nonneg
            (by linarith only [hAccelerationLower] :
              0 ≤ 12 * Real.pi ^ 2 - 113)]
        linarith only [hNearDisplayedD, hAccelerationLower]
    | C =>
        simp only [displayedAccelerationInMetersPerSecondSquared]
        rw [abs_of_nonneg
            (by linarith only [hAccelerationLower] :
              0 ≤ 12 * Real.pi ^ 2 - 108)]
        linarith only [hNearDisplayedD, hAccelerationLower]
    | D =>
        rfl

end PhyXMiniProblems.ProblemPhyXMini0240
