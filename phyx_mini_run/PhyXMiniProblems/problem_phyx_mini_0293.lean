import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0293

open Dimension

/-!
# Amplitude of a sinusoidal string wave from kinetic-energy-rate graphs

The supplied figure has two panels.  The left panel plots the rate at which
kinetic energy passes along the string against position at a fixed instant;
the right panel plots the same rate against time at a fixed position.  The
vertical scale in both panels is `Rₛ = 10 W`.

Physical lengths, times, linear mass density, speed, angular frequency, and
power are represented by unit-independent Physlib quantities.  Real numbers
occur only as coherent unit readouts, phase and wave-number scalars, or
displayed numerical answers.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical length, used for amplitude and wavelength. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration, used for the wave period. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative linear mass density, with SI unit kilogram per metre. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A nonnegative propagation speed, with SI unit metre per second. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A nonnegative angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-!
The plotted rate `dK/dt` is a power.  Its dimension is
`mass * length^2 / time^3`, whose coherent SI unit is the watt.
-/
abbrev PowerQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a duration as a real scalar in the selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Metre readout used for amplitudes, wavelengths, and the left graph. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Second readout used in the governing wave equations. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- Millisecond readout used on the right graph's horizontal axis. -/
def timeInMilliseconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.milliseconds duration

/-- Kilogram-per-metre readout of the string's linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of the wave speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Radian-per-second readout of angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Watt readout of a kinetic-energy transfer rate. -/
def powerInWatts (power : PowerQuantity) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-! ## Wave and primary-figure vocabulary -/

/-- The qualitative wave type stated in the problem. -/
inductive StringWaveKind where
  | sinusoidalTraveling
  | standing
  | other
  deriving DecidableEq, Repr

/-- The idealized string model used by the textbook relation. -/
inductive StringModelKind where
  | uniformFlexibleString
  | nonuniformString
  deriving DecidableEq, Repr

/-- Either direction of propagation along the string's `x` axis. -/
inductive PropagationDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-- Sign in the standard traveling-wave phase `kx - s * omega t + phi`. -/
def propagationDirectionSign : PropagationDirection → ℝ
  | .positiveX => 1
  | .negativeX => -1

/-- The physical rate represented by the common vertical axis. -/
inductive VerticalAxisRole where
  | kineticEnergyPassingRateWatts
  | other
  deriving DecidableEq, Repr

/-- The two distinct horizontal axes in the supplied figure. -/
inductive HorizontalAxisRole where
  | positionMeters
  | timeMilliseconds
  | other
  deriving DecidableEq, Repr

/-- The two panels in the supplied figure. -/
inductive RateGraphPanel where
  | spatialAtFixedTime
  | temporalAtFixedPosition
  deriving DecidableEq, Repr

/-- Five successive features visible from `x = 0` through `x = 0.2 m`. -/
inductive SpatialGraphFeature where
  | leftPeak
  | firstZero
  | middlePeak
  | secondZero
  | rightPeak
  deriving DecidableEq, Repr

/-- Five successive features visible from `t = 0` through `t = 2 ms`. -/
inductive TemporalGraphFeature where
  | leftPeak
  | firstZero
  | middlePeak
  | secondZero
  | rightPeak
  deriving DecidableEq, Repr

/-!
Primary-image data are stored independently from the modeled wave.  The left
panel's coordinates are physical lengths; the right panel's coordinates are
physical durations.  Both panels contain physical power values rather than
bare dimensionless ordinates.  The fixed snapshot time and probe position are
retained even though the figure does not print their numerical values.
-/
structure KineticEnergyRateFigure where
  rateScaleRs : PowerQuantity
  spatialSnapshotTime : TimeQuantity
  temporalProbePosition : LengthQuantity
  spatialCoordinate : SpatialGraphFeature → LengthQuantity
  temporalCoordinate : TemporalGraphFeature → TimeQuantity
  spatialRate : SpatialGraphFeature → PowerQuantity
  temporalRate : TemporalGraphFeature → PowerQuantity
  verticalAxisRole : RateGraphPanel → VerticalAxisRole
  horizontalAxisRole : RateGraphPanel → HorizontalAxisRole
  showsRateScaleLabelRs : RateGraphPanel → Bool
  showsSmoothNonnegativePeriodicCurve : RateGraphPanel → Bool

/-!
The independent physical quantities and observable fields of the string wave.
Arguments of `transverseDisplacementInMeters` and
`kineticEnergyPassingRate` are coherent-SI position-in-metres and
time-in-seconds readouts.  Neither function is defined from the requested
answer.
-/
structure SinusoidalStringWaveSetup where
  waveKind : StringWaveKind
  stringModel : StringModelKind
  propagationDirection : PropagationDirection
  amplitude : LengthQuantity
  wavelength : LengthQuantity
  period : TimeQuantity
  linearMassDensity : LinearMassDensityQuantity
  propagationSpeed : SpeedQuantity
  angularFrequency : AngularFrequencyQuantity
  waveNumberPerMeter : ℝ
  phaseAtOriginRadians : ℝ
  transverseDisplacementInMeters : ℝ → ℝ → ℝ
  kineticEnergyPassingRate : ℝ → ℝ → PowerQuantity
  peakKineticEnergyPassingRate : PowerQuantity
  figure : KineticEnergyRateFigure

/-! ## Assumption-side predicates -/

/-- Qualitative information stated in the physical scenario. -/
structure MatchesSinusoidalStringWaveScenario
    (setup : SinusoidalStringWaveSetup) : Prop where
  waveIsSinusoidalAndTraveling : setup.waveKind = .sinusoidalTraveling
  stringIsUniformAndFlexible : setup.stringModel = .uniformFlexibleString

/-- Positivity and nondegeneracy of the independently stored quantities. -/
structure HasPhysicalStringWaveParameters
    (setup : SinusoidalStringWaveSetup) : Prop where
  amplitudePositive : 0 < lengthInMeters setup.amplitude
  wavelengthPositive : 0 < lengthInMeters setup.wavelength
  periodPositive : 0 < timeInSeconds setup.period
  linearMassDensityPositive :
    0 < linearMassDensityInKilogramsPerMeter setup.linearMassDensity
  propagationSpeedPositive :
    0 < speedInMetersPerSecond setup.propagationSpeed
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  waveNumberPositive : 0 < setup.waveNumberPerMeter
  peakRatePositive : 0 < powerInWatts setup.peakKineticEnergyPassingRate

/-!
General laws for a traveling sinusoidal wave on a uniform string:

* `k lambda = 2 pi` and `omega T = 2 pi`;
* the wave travels one wavelength in one period, `v T = lambda`;
* the transverse displacement is sinusoidal;
* kinetic-energy density is transported at speed `v`, giving
  `dK/dt = (1/2) mu v omega^2 A^2 cos^2(phase)`;
* the corresponding peak rate is `(1/2) mu v omega^2 A^2`.

These are governing relations for arbitrary parameters.  They contain no
numerical amplitude or answer-choice value.
-/
structure SatisfiesSinusoidalStringWaveLaws
    (setup : SinusoidalStringWaveSetup) : Prop where
  waveNumberWavelengthRelation :
    setup.waveNumberPerMeter * lengthInMeters setup.wavelength = 2 * Real.pi
  angularFrequencyPeriodRelation :
    angularFrequencyInRadiansPerSecond setup.angularFrequency *
        timeInSeconds setup.period =
      2 * Real.pi
  waveSpeedRelation :
    speedInMetersPerSecond setup.propagationSpeed *
        timeInSeconds setup.period =
      lengthInMeters setup.wavelength
  sinusoidalTravelingProfile :
    ∀ xMeters timeSeconds,
      setup.transverseDisplacementInMeters xMeters timeSeconds =
        lengthInMeters setup.amplitude *
          Real.sin
            (setup.waveNumberPerMeter * xMeters -
              propagationDirectionSign setup.propagationDirection *
                angularFrequencyInRadiansPerSecond setup.angularFrequency *
                timeSeconds +
              setup.phaseAtOriginRadians)
  kineticEnergyPassingRateLaw :
    ∀ xMeters timeSeconds,
      powerInWatts (setup.kineticEnergyPassingRate xMeters timeSeconds) =
        (1 / 2 : ℝ) *
          linearMassDensityInKilogramsPerMeter setup.linearMassDensity *
          speedInMetersPerSecond setup.propagationSpeed *
          angularFrequencyInRadiansPerSecond setup.angularFrequency ^ 2 *
          lengthInMeters setup.amplitude ^ 2 *
          Real.cos
              (setup.waveNumberPerMeter * xMeters -
                propagationDirectionSign setup.propagationDirection *
                  angularFrequencyInRadiansPerSecond setup.angularFrequency *
                  timeSeconds +
                setup.phaseAtOriginRadians) ^ 2
  peakKineticEnergyPassingRateLaw :
    powerInWatts setup.peakKineticEnergyPassingRate =
      (1 / 2 : ℝ) *
        linearMassDensityInKilogramsPerMeter setup.linearMassDensity *
        speedInMetersPerSecond setup.propagationSpeed *
        angularFrequencyInRadiansPerSecond setup.angularFrequency ^ 2 *
        lengthInMeters setup.amplitude ^ 2

/-!
Primary-image evidence and the numerical datum from the problem text.

The plotted kinetic-energy rate is proportional to `cos^2` of the underlying
wave phase, so adjacent rate peaks are separated by half a wavelength in the
spatial panel and half a wave period in the temporal panel.  Those two
interpretation equations determine wavelength and period, not amplitude.
-/
structure MatchesKineticEnergyRateFigure
    (setup : SinusoidalStringWaveSetup) : Prop where
  linearDensityReadout :
    linearMassDensityInKilogramsPerMeter setup.linearMassDensity = 2 / 1000
  commonVerticalAxis :
    ∀ panel,
      setup.figure.verticalAxisRole panel = .kineticEnergyPassingRateWatts
  spatialHorizontalAxis :
    setup.figure.horizontalAxisRole .spatialAtFixedTime = .positionMeters
  temporalHorizontalAxis :
    setup.figure.horizontalAxisRole .temporalAtFixedPosition = .timeMilliseconds
  rateScaleLabels : ∀ panel, setup.figure.showsRateScaleLabelRs panel = true
  smoothPeriodicCurves :
    ∀ panel, setup.figure.showsSmoothNonnegativePeriodicCurve panel = true
  rateScaleWatts : powerInWatts setup.figure.rateScaleRs = 10
  spatialLeftPeakPosition :
    lengthInMeters (setup.figure.spatialCoordinate .leftPeak) = 0
  spatialFirstZeroPosition :
    lengthInMeters (setup.figure.spatialCoordinate .firstZero) = 1 / 20
  spatialMiddlePeakPosition :
    lengthInMeters (setup.figure.spatialCoordinate .middlePeak) = 1 / 10
  spatialSecondZeroPosition :
    lengthInMeters (setup.figure.spatialCoordinate .secondZero) = 3 / 20
  spatialRightPeakPosition :
    lengthInMeters (setup.figure.spatialCoordinate .rightPeak) = 1 / 5
  temporalLeftPeakTime :
    timeInMilliseconds (setup.figure.temporalCoordinate .leftPeak) = 0
  temporalFirstZeroTime :
    timeInMilliseconds (setup.figure.temporalCoordinate .firstZero) = 1 / 2
  temporalMiddlePeakTime :
    timeInMilliseconds (setup.figure.temporalCoordinate .middlePeak) = 1
  temporalSecondZeroTime :
    timeInMilliseconds (setup.figure.temporalCoordinate .secondZero) = 3 / 2
  temporalRightPeakTime :
    timeInMilliseconds (setup.figure.temporalCoordinate .rightPeak) = 2
  spatialPeakRates :
    (∀ point ∈
        ([SpatialGraphFeature.leftPeak, .middlePeak, .rightPeak] :
          List SpatialGraphFeature),
      powerInWatts (setup.figure.spatialRate point) =
        powerInWatts setup.figure.rateScaleRs)
  spatialZeroRates :
    (∀ point ∈
        ([SpatialGraphFeature.firstZero, .secondZero] :
          List SpatialGraphFeature),
      powerInWatts (setup.figure.spatialRate point) = 0)
  temporalPeakRates :
    (∀ point ∈
        ([TemporalGraphFeature.leftPeak, .middlePeak, .rightPeak] :
          List TemporalGraphFeature),
      powerInWatts (setup.figure.temporalRate point) =
        powerInWatts setup.figure.rateScaleRs)
  temporalZeroRates :
    (∀ point ∈
        ([TemporalGraphFeature.firstZero, .secondZero] :
          List TemporalGraphFeature),
      powerInWatts (setup.figure.temporalRate point) = 0)
  spatialSamplesModeledRate :
    ∀ point,
      powerInWatts
          (setup.kineticEnergyPassingRate
            (lengthInMeters (setup.figure.spatialCoordinate point))
            (timeInSeconds setup.figure.spatialSnapshotTime)) =
        powerInWatts (setup.figure.spatialRate point)
  temporalSamplesModeledRate :
    ∀ point,
      powerInWatts
          (setup.kineticEnergyPassingRate
            (lengthInMeters setup.figure.temporalProbePosition)
            (timeInSeconds (setup.figure.temporalCoordinate point))) =
        powerInWatts (setup.figure.temporalRate point)
  wavelengthIsTwiceAdjacentSpatialPeakSpacing :
    lengthInMeters setup.wavelength =
      2 *
        (lengthInMeters (setup.figure.spatialCoordinate .middlePeak) -
          lengthInMeters (setup.figure.spatialCoordinate .leftPeak))
  periodIsTwiceAdjacentTemporalPeakSpacing :
    timeInMilliseconds setup.period =
      2 *
        (timeInMilliseconds (setup.figure.temporalCoordinate .middlePeak) -
          timeInMilliseconds (setup.figure.temporalCoordinate .leftPeak))
  plottedScaleIsPeakRate :
    powerInWatts setup.peakKineticEnergyPassingRate =
      powerInWatts setup.figure.rateScaleRs

/-! ## Derived statements and answer choice -/

/-- The two figure periods determine `lambda = 0.2 m` and `T = 2 ms`. -/
lemma wavelength_and_period_from_rate_graphs
    (setup : SinusoidalStringWaveSetup)
    (_figure : MatchesKineticEnergyRateFigure setup) :
    lengthInMeters setup.wavelength = (1 / 5 : ℝ) ∧
      timeInMilliseconds setup.period = 2 := by
  constructor
  · rw [_figure.wavelengthIsTwiceAdjacentSpatialPeakSpacing,
      _figure.spatialMiddlePeakPosition, _figure.spatialLeftPeakPosition]
    norm_num
  · rw [_figure.periodIsTwiceAdjacentTemporalPeakSpacing,
      _figure.temporalMiddlePeakTime, _figure.temporalLeftPeakTime]
    norm_num

/-- The graph-derived scales give `v = 100 m/s` and `omega = 1000 pi rad/s`. -/
lemma speed_and_angularFrequency_from_rate_graphs
    (setup : SinusoidalStringWaveSetup)
    (_physical : HasPhysicalStringWaveParameters setup)
    (_laws : SatisfiesSinusoidalStringWaveLaws setup)
    (_figure : MatchesKineticEnergyRateFigure setup) :
    speedInMetersPerSecond setup.propagationSpeed = 100 ∧
      angularFrequencyInRadiansPerSecond setup.angularFrequency =
        1000 * Real.pi := by
  obtain ⟨hWavelength, hTms⟩ :=
    wavelength_and_period_from_rate_graphs setup _figure
  have hTscale := setup.period.2 UnitChoices.SI
    {UnitChoices.SI with time := TimeUnit.milliseconds}
  have hTscaleVal := congrArg
    (fun q : WithDim T𝓭 NNReal => (q.val : ℝ)) hTscale
  have hTseconds : timeInSeconds setup.period = (1 / 500 : ℝ) := by
    simp only [WithDim.smul_val] at hTscaleVal
    change timeInMilliseconds setup.period =
      (((UnitChoices.SI.dimScale
        {UnitChoices.SI with time := TimeUnit.milliseconds} T𝓭 : NNReal) : ℝ) *
        timeInSeconds setup.period) at hTscaleVal
    norm_num [UnitChoices.dimScale, TimeUnit.milliseconds, TimeUnit.scale,
      TimeUnit.div_eq_val, TimeUnit.seconds] at hTscaleVal
    change timeInMilliseconds setup.period =
      1000 * timeInSeconds setup.period at hTscaleVal
    linarith
  constructor
  · nlinarith [_laws.waveSpeedRelation]
  · have hAngularFrequency := _laws.angularFrequencyPeriodRelation
    rw [hTseconds] at hAngularFrequency
    nlinarith

/-- Labels attached to the four amplitudes printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Amplitude in metres printed beside each answer label. -/
def displayedAmplitudeInMeters : AnswerChoice → ℝ
  | .A => 25 / 10000
  | .B => 28 / 10000
  | .C => 30 / 10000
  | .D => 32 / 10000

/-- Dataset provenance retained separately from the physical premises. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement after rounding an exact amplitude to four decimal metres. -/
def RoundsToDisplayedFourDecimalMeters
    (amplitude : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters amplitude - displayedAmplitudeInMeters choice| ≤
    (1 / 20000 : ℝ)

/-- The selected answer is the unique displayed value matching the amplitude. -/
def IsUniqueMatchingAnswerChoice
    (setup : SinusoidalStringWaveSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedFourDecimalMeters setup.amplitude choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedFourDecimalMeters setup.amplitude other → other = choice

/-!
From the two graph periods, `lambda = 0.2 m`, `T = 0.002 s`,
`v = 100 m/s`, and `omega = 1000 pi rad/s`.  With
`mu = 0.002 kg/m` and peak kinetic-energy passing rate `10 W`, the law

`R_max = (1/2) mu v omega^2 A^2`

gives the exact amplitude `A = 1 / (100 pi) m`.
-/
lemma exact_amplitude_from_kineticEnergy_rate
    (setup : SinusoidalStringWaveSetup)
    (_scenario : MatchesSinusoidalStringWaveScenario setup)
    (_physical : HasPhysicalStringWaveParameters setup)
    (_laws : SatisfiesSinusoidalStringWaveLaws setup)
    (_figure : MatchesKineticEnergyRateFigure setup) :
    lengthInMeters setup.amplitude = (1 / 100 : ℝ) / Real.pi := by
  obtain ⟨hSpeed, hAngularFrequency⟩ :=
    speed_and_angularFrequency_from_rate_graphs setup _physical _laws _figure
  have hPeakRate :
      powerInWatts setup.peakKineticEnergyPassingRate = 10 :=
    _figure.plottedScaleIsPeakRate.trans _figure.rateScaleWatts
  have hPower := _laws.peakKineticEnergyPassingRateLaw
  rw [hPeakRate, _figure.linearDensityReadout, hSpeed, hAngularFrequency] at hPower
  norm_num at hPower
  have hAmplitudePiPositive :
      0 < lengthInMeters setup.amplitude * Real.pi :=
    mul_pos _physical.amplitudePositive Real.pi_pos
  apply (eq_div_iff (ne_of_gt Real.pi_pos)).2
  nlinarith [sq_nonneg
    (lengthInMeters setup.amplitude * Real.pi - (1 / 100 : ℝ))]

/-!
The exact amplitude `1 / (100 pi) m` is approximately `0.003183 m`; to the
precision of the displayed choices it is `0.0032 m`, uniquely selecting D.
The exact amplitude and answer selection are conclusions, not premises.

This formalizes blueprint label `thm:physics:phyx_mini_0293:target`.
-/
theorem problem_phyx_mini_0293
    (setup : SinusoidalStringWaveSetup)
    (_scenario : MatchesSinusoidalStringWaveScenario setup)
    (_physical : HasPhysicalStringWaveParameters setup)
    (_laws : SatisfiesSinusoidalStringWaveLaws setup)
    (_figure : MatchesKineticEnergyRateFigure setup) :
    lengthInMeters setup.amplitude = (1 / 100 : ℝ) / Real.pi ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hAmplitude :=
    exact_amplitude_from_kineticEnergy_rate
      setup _scenario _physical _laws _figure
  refine ⟨hAmplitude, ?_⟩
  have hAmplitudeLower :
      (63 / 20000 : ℝ) < (1 / 100 : ℝ) / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  have hAmplitudeUpper :
      (1 / 100 : ℝ) / Real.pi < (13 / 4000 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d2]
  change RoundsToDisplayedFourDecimalMeters setup.amplitude .D ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedFourDecimalMeters setup.amplitude other → other = .D
  constructor
  · change
      |lengthInMeters setup.amplitude - 32 / 10000| ≤ (1 / 20000 : ℝ)
    rw [hAmplitude, abs_le]
    constructor <;> nlinarith
  · intro other hOther
    cases other with
    | A =>
        change
          |lengthInMeters setup.amplitude - 25 / 10000| ≤
            (1 / 20000 : ℝ) at hOther
        rw [hAmplitude, abs_le] at hOther
        exfalso
        nlinarith
    | B =>
        change
          |lengthInMeters setup.amplitude - 28 / 10000| ≤
            (1 / 20000 : ℝ) at hOther
        rw [hAmplitude, abs_le] at hOther
        exfalso
        nlinarith
    | C =>
        change
          |lengthInMeters setup.amplitude - 30 / 10000| ≤
            (1 / 20000 : ℝ) at hOther
        rw [hAmplitude, abs_le] at hOther
        exfalso
        nlinarith
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0293
