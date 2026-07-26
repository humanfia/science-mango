import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Pressure
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0309

open Dimension

/-!
# Wave number from an acoustic pressure-versus-time graph

A pressure monitor is fixed at one point of a single-frequency plane sound
wave in air.  The primary figure plots the signed pressure change `Δp` in
millipascals against time in milliseconds.  Its positive peaks occur at
`-0.5 ms` and `1.5 ms`, so the measured period is `2 ms`.

Physical durations, positions, speeds, pressures, mass density, displacement
amplitude, frequency, angular frequency, and wave number are represented by
Physlib `Dimensionful` quantities.  Real numbers below are only coordinate or
unit readouts, signed scalar components, dimensionless phases, and displayed
answer values.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed time coordinate, as needed for the negative times in the graph. -/
abbrev SignedTimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A nonnegative physical length or displacement amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed position coordinate along the sound-wave path. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Propagation speed of the sound wave. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Signed acoustic pressure change. -/
abbrev PressureQuantity : Type := DimPressure

/-- Uniform mass density, with dimension mass per volume. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- Cyclic frequency, whose SI readout is in hertz. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Angular frequency, with radians treated as dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Wave number, with radians treated as dimensionless. -/
abbrev WaveNumberQuantity : Type :=
  Dimensionful (WithDim L𝓭⁻¹ NNReal)

/-- Read a nonnegative duration in the selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration { UnitChoices.SI with time := unit }).val : ℝ)

/-- Read a signed time coordinate in the selected time unit. -/
def signedTimeReadout
    (unit : TimeUnit) (time : SignedTimeQuantity) : ℝ :=
  (time { UnitChoices.SI with time := unit }).val

/-- Read a nonnegative length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length { UnitChoices.SI with length := unit }).val : ℝ)

/-- Read a signed position in the selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (position : SignedLengthQuantity) : ℝ :=
  (position { UnitChoices.SI with length := unit }).val

/-- Read a speed in the selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed { UnitChoices.SI with
      length := lengthUnit
      time := timeUnit }).val : ℝ)

/-- SI readout of a pressure change, in pascals. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Pressure readout in millipascals, the vertical unit in the figure. -/
def pressureInMillipascals (pressure : PressureQuantity) : ℝ :=
  1000 * pressureInPascals pressure

/-- SI readout of mass density, in kilograms per cubic metre. -/
def massDensityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Hertz readout of the physical cyclic frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Radian-per-second readout of angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : AngularFrequencyQuantity) : ℝ :=
  ((angularFrequency UnitChoices.SI).val : ℝ)

/-- Radian-per-metre readout of wave number. -/
def waveNumberInRadiansPerMeter (waveNumber : WaveNumberQuantity) : ℝ :=
  ((waveNumber UnitChoices.SI).val : ℝ)

/-! ## Primary-figure labels and acoustic setup -/

/-- Roles of the three mathematical labels printed in the primary figure. -/
inductive FigureLabelRole where
  | horizontalAxis
  | verticalAxis
  | pressureScale
  deriving DecidableEq, Repr

/-- Mathematical symbols printed in the primary figure. -/
inductive FigureLabel where
  | t
  | deltaP
  | deltaPSubS
  deriving DecidableEq, Repr

/-- Unit displayed on the pressure axis. -/
inductive PressureDisplayUnit where
  | pascals
  | millipascals
  deriving DecidableEq, Repr

/-- Distinguished times visible on the plotted sinusoid. -/
inductive FigureTimeMark where
  | leftZero
  | firstPositivePeak
  | timeOrigin
  | negativeTrough
  | oneMillisecondZero
  | secondPositivePeak
  | rightZero
  deriving DecidableEq, Repr

/-- The propagation medium explicitly specified by the problem. -/
inductive AcousticMedium where
  | air
  deriving DecidableEq, Repr

/-- The pressure-versus-time monitor figure and its dimensionful readouts. -/
structure PressureTimeFigure where
  label : FigureLabelRole → FigureLabel
  timeUnit : TimeUnit
  pressureUnit : PressureDisplayUnit
  timeAt : FigureTimeMark → SignedTimeQuantity
  pressureChangeAt : FigureTimeMark → PressureQuantity
  deltaPScale : PressureQuantity

/-!
The independent physical quantities and fields in the acoustic experiment.

`displacementInMeters x t` is the signed longitudinal displacement component
in metres at an SI position `x` and SI time `t`.  The pressure field returns a
physical `DimPressure`; its argument is an SI time coordinate in seconds.
-/
structure AcousticPressureMonitorSetup where
  medium : AcousticMedium
  uniformAirMassDensity : MassDensityQuantity
  propagationSpeed : SpeedQuantity
  wavePeriod : TimeQuantity
  cyclicFrequency : FrequencyQuantity
  angularFrequency : AngularFrequencyQuantity
  waveNumber : WaveNumberQuantity
  displacementAmplitude : LengthQuantity
  pressureAmplitude : PressureQuantity
  monitorPosition : SignedLengthQuantity
  displacementInMeters : ℝ → ℝ → ℝ
  pressureChangeAtMonitorSeconds : ℝ → PressureQuantity
  figure : PressureTimeFigure

/-!
Data transcribed from the statement and the primary image.  The graph has
zeros at `-1, 0, 1, 2 ms`, positive peaks at `-0.5, 1.5 ms`, and a trough at
`0.5 ms`.  The `Δp_s` marks lie halfway between zero and the extrema, so the
peak magnitude is twice the stated `4.0 mPa` scale.

The period field is tied to the separation of equal positive peaks.  No field
mentions the requested wave number or any answer-choice value.
-/
structure MatchesProblemStatementAndFigure
    (setup : AcousticPressureMonitorSetup) : Prop where
  mediumIsAir : setup.medium = .air
  soundSpeedMetersPerSecond :
    speedReadout LengthUnit.meters TimeUnit.seconds
        setup.propagationSpeed = 343
  uniformDensityKilogramsPerCubicMeter :
    massDensityInKilogramsPerCubicMeter setup.uniformAirMassDensity =
      121 / 100
  horizontalAxisLabelIsTime :
    setup.figure.label .horizontalAxis = .t
  verticalAxisLabelIsPressureChange :
    setup.figure.label .verticalAxis = .deltaP
  pressureScaleLabelIsDeltaPSubS :
    setup.figure.label .pressureScale = .deltaPSubS
  timeAxisUsesMilliseconds :
    setup.figure.timeUnit = TimeUnit.milliseconds
  pressureAxisUsesMillipascals :
    setup.figure.pressureUnit = .millipascals
  pressureScaleMillipascals :
    pressureInMillipascals setup.figure.deltaPScale = 4
  leftZeroTimeMilliseconds :
    signedTimeReadout TimeUnit.milliseconds
        (setup.figure.timeAt .leftZero) = -1
  firstPositivePeakTimeMilliseconds :
    signedTimeReadout TimeUnit.milliseconds
        (setup.figure.timeAt .firstPositivePeak) = -(1 / 2)
  timeOriginMilliseconds :
    signedTimeReadout TimeUnit.milliseconds
        (setup.figure.timeAt .timeOrigin) = 0
  negativeTroughTimeMilliseconds :
    signedTimeReadout TimeUnit.milliseconds
        (setup.figure.timeAt .negativeTrough) = 1 / 2
  oneMillisecondZeroTime :
    signedTimeReadout TimeUnit.milliseconds
        (setup.figure.timeAt .oneMillisecondZero) = 1
  secondPositivePeakTimeMilliseconds :
    signedTimeReadout TimeUnit.milliseconds
        (setup.figure.timeAt .secondPositivePeak) = 3 / 2
  rightZeroTimeMilliseconds :
    signedTimeReadout TimeUnit.milliseconds
        (setup.figure.timeAt .rightZero) = 2
  plottedCurveAtMarkedTimes :
    ∀ mark : FigureTimeMark,
      setup.pressureChangeAtMonitorSeconds
          (signedTimeReadout TimeUnit.seconds
            (setup.figure.timeAt mark)) =
        setup.figure.pressureChangeAt mark
  leftZeroPressure :
    pressureInMillipascals
        (setup.figure.pressureChangeAt .leftZero) = 0
  originPressure :
    pressureInMillipascals
        (setup.figure.pressureChangeAt .timeOrigin) = 0
  oneMillisecondZeroPressure :
    pressureInMillipascals
        (setup.figure.pressureChangeAt .oneMillisecondZero) = 0
  rightZeroPressure :
    pressureInMillipascals
        (setup.figure.pressureChangeAt .rightZero) = 0
  firstPositivePeakIsAmplitude :
    setup.figure.pressureChangeAt .firstPositivePeak =
      setup.pressureAmplitude
  secondPositivePeakIsAmplitude :
    setup.figure.pressureChangeAt .secondPositivePeak =
      setup.pressureAmplitude
  positivePeakIsTwiceScale :
    pressureInMillipascals setup.pressureAmplitude =
      2 * pressureInMillipascals setup.figure.deltaPScale
  negativeTroughIsNegativeAmplitude :
    pressureInMillipascals
        (setup.figure.pressureChangeAt .negativeTrough) =
      -pressureInMillipascals setup.pressureAmplitude
  monitorChosenAsSpatialOrigin :
    signedLengthReadout LengthUnit.meters setup.monitorPosition = 0
  periodIsPositivePeakSeparation :
    ∀ unit : TimeUnit,
      timeReadout unit setup.wavePeriod =
        signedTimeReadout unit
            (setup.figure.timeAt .secondPositivePeak) -
          signedTimeReadout unit
            (setup.figure.timeAt .firstPositivePeak)

/-- Positivity and nondegeneracy conditions for the physical sound wave. -/
structure HasPhysicalAcousticParameters
    (setup : AcousticPressureMonitorSetup) : Prop where
  densityPositive :
    0 < massDensityInKilogramsPerCubicMeter setup.uniformAirMassDensity
  propagationSpeedPositive :
    0 < speedReadout LengthUnit.meters TimeUnit.seconds
      setup.propagationSpeed
  periodPositive :
    0 < timeReadout TimeUnit.seconds setup.wavePeriod
  cyclicFrequencyPositive :
    0 < frequencyInHertz setup.cyclicFrequency
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  waveNumberPositive :
    0 < waveNumberInRadiansPerMeter setup.waveNumber
  displacementAmplitudePositive :
    0 < lengthReadout LengthUnit.meters setup.displacementAmplitude
  pressureAmplitudePositive :
    0 < pressureInPascals setup.pressureAmplitude
  pressureScalePositive :
    0 < pressureInPascals setup.figure.deltaPScale

/-!
The governing laws of the idealized nondispersive plane sound wave:

* `s(x,t) = s_m cos(kx - ωt)`, exactly as stated in the question;
* the monitor pressure has the corresponding quadrature sinusoid;
* cyclic frequency and period obey `f T = 1`;
* angular frequency obeys `ω = 2πf`;
* nondispersive phase speed obeys `ω = kv`;
* the pressure amplitude obeys `Δp_m = ρ v ω s_m`.

These are general physical relations.  They contain neither the requested
closed form `1000π/343` nor the displayed value `9.2 rad/m`.
-/
structure SatisfiesSingleFrequencyPlaneSoundWaveLaws
    (setup : AcousticPressureMonitorSetup) : Prop where
  displacementNormalForm :
    ∀ (xMeters tSeconds : ℝ),
      setup.displacementInMeters xMeters tSeconds =
        lengthReadout LengthUnit.meters setup.displacementAmplitude *
          Real.cos
            (waveNumberInRadiansPerMeter setup.waveNumber * xMeters -
              angularFrequencyInRadiansPerSecond setup.angularFrequency *
                tSeconds)
  monitorPressureNormalForm :
    ∀ tSeconds : ℝ,
      pressureInPascals
          (setup.pressureChangeAtMonitorSeconds tSeconds) =
        pressureInPascals setup.pressureAmplitude *
          Real.sin
            (waveNumberInRadiansPerMeter setup.waveNumber *
                signedLengthReadout LengthUnit.meters
                  setup.monitorPosition -
              angularFrequencyInRadiansPerSecond setup.angularFrequency *
                tSeconds)
  frequencyPeriodRelation :
    frequencyInHertz setup.cyclicFrequency *
        timeReadout TimeUnit.seconds setup.wavePeriod = 1
  angularFrequencyFromCyclicFrequency :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      2 * Real.pi * frequencyInHertz setup.cyclicFrequency
  nondispersiveWaveSpeedRelation :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      waveNumberInRadiansPerMeter setup.waveNumber *
        speedReadout LengthUnit.meters TimeUnit.seconds
          setup.propagationSpeed
  planeWavePressureAmplitudeRelation :
    pressureInPascals setup.pressureAmplitude =
      massDensityInKilogramsPerCubicMeter setup.uniformAirMassDensity *
        speedReadout LengthUnit.meters TimeUnit.seconds
          setup.propagationSpeed *
        angularFrequencyInRadiansPerSecond setup.angularFrequency *
        lengthReadout LengthUnit.meters setup.displacementAmplitude

/-! ## Derived readouts and final answer -/

/-- The peak-to-peak separation in the graph gives a period of `2 ms`. -/
lemma wavePeriodInMilliseconds_eq_two
    (setup : AcousticPressureMonitorSetup)
    (hData : MatchesProblemStatementAndFigure setup) :
    timeReadout TimeUnit.milliseconds setup.wavePeriod = 2 := by
  rw [hData.periodIsPositivePeakSeparation,
    hData.secondPositivePeakTimeMilliseconds,
    hData.firstPositivePeakTimeMilliseconds]
  norm_num

/-- A `2 ms` period corresponds to a cyclic frequency of `500 Hz`. -/
lemma cyclicFrequencyInHertz_eq_fiveHundred
    (setup : AcousticPressureMonitorSetup)
    (hData : MatchesProblemStatementAndFigure setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hLaws : SatisfiesSingleFrequencyPlaneSoundWaveLaws setup) :
    frequencyInHertz setup.cyclicFrequency = 500 := by
  have hPeriodMilliseconds :=
    wavePeriodInMilliseconds_eq_two setup hData
  let milliseconds : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.milliseconds}
  let seconds : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.seconds}
  have hTimeScale :
      milliseconds.dimScale seconds T𝓭 =
        (⟨1 / 1000, by norm_num⟩ : NNReal) := by
    norm_num [milliseconds, seconds, UnitChoices.dimScale,
      TimeUnit.milliseconds, TimeUnit.seconds]
  have hPeriodUnits :=
    congrArg (fun quantity : WithDim T𝓭 NNReal => (quantity.val : ℝ))
      (setup.wavePeriod.2 milliseconds seconds)
  rw [show dim (WithDim T𝓭 NNReal) = T𝓭 by rfl, hTimeScale] at hPeriodUnits
  dsimp [seconds, milliseconds] at hPeriodUnits
  norm_num at hPeriodUnits
  change timeReadout TimeUnit.seconds setup.wavePeriod =
    (1 / 1000 : ℝ) *
      timeReadout TimeUnit.milliseconds setup.wavePeriod at hPeriodUnits
  rw [hPeriodMilliseconds] at hPeriodUnits
  norm_num at hPeriodUnits
  have hFrequencyPeriod := hLaws.frequencyPeriodRelation
  rw [hPeriodUnits] at hFrequencyPeriod
  linarith

/-- The graph period gives angular frequency `1000π rad/s`. -/
lemma angularFrequencyInRadiansPerSecond_eq_oneThousand_pi
    (setup : AcousticPressureMonitorSetup)
    (hData : MatchesProblemStatementAndFigure setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hLaws : SatisfiesSingleFrequencyPlaneSoundWaveLaws setup) :
    angularFrequencyInRadiansPerSecond setup.angularFrequency =
      1000 * Real.pi := by
  rw [hLaws.angularFrequencyFromCyclicFrequency,
    cyclicFrequencyInHertz_eq_fiveHundred setup hData hPhysical hLaws]
  ring

/-!
Using `ω = kv` and the stated speed `343 m/s`, the exact wave number is
`1000π/343 rad/m`.
-/
lemma waveNumberInRadiansPerMeter_eq_oneThousand_pi_div_343
    (setup : AcousticPressureMonitorSetup)
    (hData : MatchesProblemStatementAndFigure setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hLaws : SatisfiesSingleFrequencyPlaneSoundWaveLaws setup) :
    waveNumberInRadiansPerMeter setup.waveNumber =
      1000 * Real.pi / 343 := by
  have hWaveSpeed := hLaws.nondispersiveWaveSpeedRelation
  rw [angularFrequencyInRadiansPerSecond_eq_oneThousand_pi
      setup hData hPhysical hLaws,
    hData.soundSpeedMetersPerSecond] at hWaveSpeed
  apply (eq_div_iff (by norm_num : (343 : ℝ) ≠ 0)).2
  exact hWaveSpeed.symm

/-- Labels printed beside the four candidate wave numbers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Radian-per-metre value printed beside each answer label. -/
def AnswerChoice.radiansPerMeter : AnswerChoice → ℝ
  | .A => 8
  | .B => 42 / 5
  | .C => 44 / 5
  | .D => 46 / 5

/-- The answer label recorded in the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a value displayed to the nearest tenth of a radian per metre.
The strict half-width excludes a midpoint tie.
-/
def MatchesNearestTenthDisplay
    (waveNumberRadiansPerMeter : ℝ) (choice : AnswerChoice) : Prop :=
  |waveNumberRadiansPerMeter - choice.radiansPerMeter| < (1 : ℝ) / 20

/-!
The primary image gives `T = 2 ms`, hence `f = 500 Hz` and
`ω = 1000π rad/s`.  With speed `343 m/s`,
`k = 1000π/343 rad/m`, whose nearest-tenth display is `9.2 rad/m`, choice D.

This formalizes blueprint label `thm:physics:phyx_mini_0309:target`.
-/
theorem problem_phyx_mini_0309
    (setup : AcousticPressureMonitorSetup)
    (hData : MatchesProblemStatementAndFigure setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hLaws : SatisfiesSingleFrequencyPlaneSoundWaveLaws setup) :
    waveNumberInRadiansPerMeter setup.waveNumber =
        1000 * Real.pi / 343 ∧
      MatchesNearestTenthDisplay
        (waveNumberInRadiansPerMeter setup.waveNumber)
        recordedAnswerChoice := by
  have hWaveNumber :=
    waveNumberInRadiansPerMeter_eq_oneThousand_pi_div_343
      setup hData hPhysical hLaws
  refine ⟨hWaveNumber, ?_⟩
  have hSqrtTwoNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hSqrtTwoSquared : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hSqrtTwoLower : (1.4142 : ℝ) < Real.sqrt 2 := by
    nlinarith only [hSqrtTwoNonnegative, hSqrtTwoSquared]
  have hSqrtTwoUpper : Real.sqrt 2 < (1.41422 : ℝ) := by
    nlinarith only [hSqrtTwoNonnegative, hSqrtTwoSquared]
  have hNestedSqrtNonnegative :
      0 ≤ Real.sqrt (2 + Real.sqrt 2) := Real.sqrt_nonneg _
  have hNestedSqrtSquared :
      (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hNestedSqrtLower :
      (1.8471 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    nlinarith only [hNestedSqrtNonnegative, hNestedSqrtSquared,
      hSqrtTwoLower]
  have hNestedSqrtUpper :
      Real.sqrt (2 + Real.sqrt 2) < (1.84777 : ℝ) := by
    nlinarith only [hNestedSqrtNonnegative, hNestedSqrtSquared,
      hSqrtTwoUpper]
  have hSinPiDivSixteenPositive :
      0 < Real.sin (Real.pi / 16) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith only [Real.pi_pos]
  have hSinPiDivSixteenSquared :
      Real.sin (Real.pi / 16) ^ 2 =
        (2 - Real.sqrt (2 + Real.sqrt 2)) / 4 := by
    have h := Real.sin_sq_pi_over_two_pow_succ 2
    norm_num [Real.sqrtTwoAddSeries] at h ⊢
    nlinarith only [h]
  have hSinPiDivSixteenLower :
      (0.19508 : ℝ) < Real.sin (Real.pi / 16) := by
    nlinarith only [hSinPiDivSixteenPositive, hSinPiDivSixteenSquared,
      hNestedSqrtUpper,
      sq_nonneg (Real.sin (Real.pi / 16) - 0.19508)]
  have hSinPiDivSixteenUpper :
      Real.sin (Real.pi / 16) < (0.19552 : ℝ) := by
    nlinarith only [hSinPiDivSixteenPositive, hSinPiDivSixteenSquared,
      hNestedSqrtLower,
      sq_nonneg (Real.sin (Real.pi / 16) - 0.19552)]
  have hSinThreePointFourteenUpper :
      Real.sin (3.14 / 16) < (0.19508 : ℝ) := by
    have h := Real.sin_bound (x := (3.14 : ℝ) / 16) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.14 / 16)] at h
    rcases abs_le.mp h with ⟨_, hUpper⟩
    norm_num at hUpper ⊢
    linarith only [hUpper]
  have hSinThreePointFifteenLower :
      (0.19552 : ℝ) < Real.sin (3.15 / 16) := by
    have h := Real.sin_bound (x := (3.15 : ℝ) / 16) (by norm_num)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3.15 / 16)] at h
    rcases abs_le.mp h with ⟨hLower, _⟩
    norm_num at hLower ⊢
    linarith only [hLower]
  have hPiLower : (3.14 : ℝ) < Real.pi := by
    by_contra hPi
    have hPiLe : Real.pi ≤ (3.14 : ℝ) := le_of_not_gt hPi
    have hSinMonotone :
        Real.sin (Real.pi / 16) ≤ Real.sin (3.14 / 16) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.one_le_pi_div_two]
      · nlinarith only [hPiLe]
    linarith only [hSinPiDivSixteenLower, hSinMonotone,
      hSinThreePointFourteenUpper]
  have hPiUpper : Real.pi < (3.15 : ℝ) := by
    by_contra hPi
    have hPiGe : (3.15 : ℝ) ≤ Real.pi := le_of_not_gt hPi
    have hSinMonotone :
        Real.sin (3.15 / 16) ≤ Real.sin (Real.pi / 16) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.pi_pos]
      · nlinarith only [hPiGe]
    linarith only [hSinThreePointFifteenLower, hSinMonotone,
      hSinPiDivSixteenUpper]
  rw [MatchesNearestTenthDisplay, hWaveNumber, abs_lt]
  simp only [recordedAnswerChoice, AnswerChoice.radiansPerMeter]
  constructor <;> norm_num at ⊢
  · nlinarith only [hPiLower]
  · nlinarith only [hPiUpper]

end PhyXMiniProblems.ProblemPhyXMini0309
