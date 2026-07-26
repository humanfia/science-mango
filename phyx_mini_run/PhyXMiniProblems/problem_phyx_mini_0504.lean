import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0504

open Dimension

/-!
# Maximum rate of a bandwidth-limited rectangular pulse train

The primary figure shows a periodic rectangular pulse train.  Each high pulse
has duration `Delta t`, and the start-to-start period is labelled
`T = 2 Delta t`.  The electronics system has a bandwidth of `200 kHz`.

Durations, bandwidths, and pulse rates are represented by unit-independent
Physlib quantities.  Real numbers below occur only as readouts in named time
units or as the dimensionless number of transmitted pulses per unit time.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical duration, carrying the dimension of time. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical duration in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical inverse-time quantity in the inverse selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Duration readout in seconds. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Frequency readout in hertz, i.e. inverse seconds. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Bandwidth readout in kilohertz, i.e. inverse milliseconds. -/
def bandwidthInKilohertz (bandwidth : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.milliseconds bandwidth

/-- A pulse-rate readout in pulses per second; pulse count is dimensionless. -/
def pulseRateInPulsesPerSecond (rate : FrequencyQuantity) : ℝ :=
  frequencyInHertz rate

/-! ## Physical setup and primary-figure labels -/

/-- The waveform shape visible in the primary image. -/
inductive PulseTrainShape where
  | periodicRectangularPulses
  | otherWaveform
  deriving DecidableEq, Repr

/-- Roles of the labels printed in the primary image. -/
inductive FigureLabelRole where
  | horizontalAxis
  | pulseWidthArrow
  | periodArrow
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the primary image. -/
inductive FigureLabel where
  | timeT
  | deltaT
  | periodTEqualsTwoDeltaT
  deriving DecidableEq, Repr

/-- The two time intervals marked by double-headed arrows in the figure. -/
inductive FigureDurationMark where
  | pulseWidth
  | startToStartPeriod
  deriving DecidableEq, Repr

/-- The labelled rectangular-pulse figure and its dimensionful arrow data. -/
structure PulseTrainFigure where
  shape : PulseTrainShape
  label : FigureLabelRole → FigureLabel
  markedDuration : FigureDurationMark → DurationQuantity

/-!
The independent physical quantities in the bandwidth-limited pulse system.

The maximum rate is an independent inverse-time quantity.  Its relation to
the independent period, pulse duration, and bandwidth is imposed only by the
general laws below; no numerical answer is built into this structure.
-/
structure BandwidthLimitedPulseTrain where
  figure : PulseTrainFigure
  pulseDuration : DurationQuantity
  period : DurationQuantity
  systemBandwidth : FrequencyQuantity
  maximumPulseTransmissionRate : FrequencyQuantity

/-!
Data transcribed from the prose and the primary image: a periodic rectangular
pulse train, horizontal time axis `t`, pulse-width arrow `Delta t`, period
arrow `T = 2 Delta t`, and `200 kHz` electronics bandwidth.

The last-but-one field is the semantic content of the period label, stated in
every time unit.  No maximum-rate value or answer choice occurs here.
-/
structure MatchesProblemStatementAndFigure
    (setup : BandwidthLimitedPulseTrain) : Prop where
  waveformIsPeriodicRectangularPulseTrain :
    setup.figure.shape = .periodicRectangularPulses
  horizontalAxisLabelIsTime :
    setup.figure.label .horizontalAxis = .timeT
  pulseWidthArrowLabelIsDeltaT :
    setup.figure.label .pulseWidthArrow = .deltaT
  periodArrowCarriesDisplayedFormula :
    setup.figure.label .periodArrow = .periodTEqualsTwoDeltaT
  pulseWidthArrowMarksPulseDuration :
    setup.figure.markedDuration .pulseWidth = setup.pulseDuration
  periodArrowMarksStartToStartPeriod :
    setup.figure.markedDuration .startToStartPeriod = setup.period
  displayedPeriodRelation : ∀ unit : TimeUnit,
    durationReadout unit setup.period =
      2 * durationReadout unit setup.pulseDuration
  statedSystemBandwidthKilohertz :
    bandwidthInKilohertz setup.systemBandwidth = 200

/-- Positivity conditions for a nondegenerate pulse train and electronics system. -/
structure HasPhysicalPulseTrainParameters
    (setup : BandwidthLimitedPulseTrain) : Prop where
  pulseDurationPositive :
    0 < durationInSeconds setup.pulseDuration
  periodPositive :
    0 < durationInSeconds setup.period
  bandwidthPositive :
    0 < frequencyInHertz setup.systemBandwidth
  maximumRatePositive :
    0 < pulseRateInPulsesPerSecond setup.maximumPulseTransmissionRate

/-!
The ideal bandwidth-limited resolution model used by the numerical problem.

At the limiting pulse width the reciprocal bandwidth-duration relation is
`B Delta-t = 1`.  A periodic train sends one pulse per start-to-start period,
so its limiting pulse rate obeys `R T = 1`.  Both laws are expressed in every
time unit and contain neither `100000 pulses/s` nor answer label C.
-/
structure SatisfiesIdealPulseBandwidthLaws
    (setup : BandwidthLimitedPulseTrain) : Prop where
  limitingBandwidthDurationRelation : ∀ unit : TimeUnit,
    frequencyReadout unit setup.systemBandwidth *
        durationReadout unit setup.pulseDuration = 1
  onePulsePerPeriodRelation : ∀ unit : TimeUnit,
    frequencyReadout unit setup.maximumPulseTransmissionRate *
        durationReadout unit setup.period = 1

/-! ## Displayed answer data -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Pulse-rate number printed beside each choice, in pulses per second. -/
def displayedPulseRateInPulsesPerSecond : AnswerChoice → ℝ
  | .A => 1000
  | .B => 10000000
  | .C => 100000
  | .D => 1000000

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A physical maximum pulse rate agrees with the value printed for a choice. -/
def MatchesAnswerChoice
    (setup : BandwidthLimitedPulseTrain) (choice : AnswerChoice) : Prop :=
  pulseRateInPulsesPerSecond setup.maximumPulseTransmissionRate =
    displayedPulseRateInPulsesPerSecond choice

/-!
For an ideal pulse train with `T = 2 Delta-t`, the limiting reciprocal laws
give a maximum rate equal to one half of the system bandwidth.  This is a
derived relation, not a law field or setup definition.
-/
lemma maximum_pulse_rate_is_half_bandwidth
    (setup : BandwidthLimitedPulseTrain)
    (hphysical : HasPhysicalPulseTrainParameters setup)
    (hfigure : MatchesProblemStatementAndFigure setup)
    (hlaws : SatisfiesIdealPulseBandwidthLaws setup)
    (unit : TimeUnit) :
    frequencyReadout unit setup.maximumPulseTransmissionRate =
      frequencyReadout unit setup.systemBandwidth / 2 := by
  have hperiod := hfigure.displayedPeriodRelation unit
  have hbandwidth := hlaws.limitingBandwidthDurationRelation unit
  have hrate := hlaws.onePulsePerPeriodRelation unit
  have hduration_ne : durationReadout unit setup.pulseDuration ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hbandwidth
    norm_num at hbandwidth
  rw [hperiod] at hrate
  apply mul_right_cancel₀ hduration_ne
  nlinarith [hbandwidth, hrate]

/-!
A bandwidth of `200 kHz` therefore permits at most `100 kHz`, or
`1.0 * 10^5 pulses/s`, for the depicted 50%-duty pulse train.  This is the
displayed answer C.

This formalizes `thm:physics:phyx_mini_0504:target`.
-/
theorem problem_phyx_mini_0504
    (setup : BandwidthLimitedPulseTrain)
    (hphysical : HasPhysicalPulseTrainParameters setup)
    (hfigure : MatchesProblemStatementAndFigure setup)
    (hlaws : SatisfiesIdealPulseBandwidthLaws setup) :
    pulseRateInPulsesPerSecond setup.maximumPulseTransmissionRate = 100000 ∧
      MatchesAnswerChoice setup recordedDatasetAnswer := by
  let milliseconds : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.milliseconds}
  let seconds : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.seconds}
  have hFrequencyScale :
      milliseconds.dimScale seconds T𝓭⁻¹ =
        (⟨1000, by norm_num⟩ : NNReal) := by
    rw [UnitChoices.dimScale_of_inv_eq_swap]
    norm_num [milliseconds, seconds, UnitChoices.dimScale,
      TimeUnit.milliseconds, TimeUnit.seconds]
  have hBandwidthUnits :=
    congrArg (fun quantity : WithDim T𝓭⁻¹ NNReal => (quantity.val : ℝ))
      (setup.systemBandwidth.2 milliseconds seconds)
  rw [show dim (WithDim T𝓭⁻¹ NNReal) = T𝓭⁻¹ by rfl,
    hFrequencyScale] at hBandwidthUnits
  dsimp [seconds, milliseconds] at hBandwidthUnits
  change frequencyReadout TimeUnit.seconds setup.systemBandwidth =
    1000 * bandwidthInKilohertz setup.systemBandwidth at hBandwidthUnits
  rw [hfigure.statedSystemBandwidthKilohertz] at hBandwidthUnits
  norm_num at hBandwidthUnits
  have hrate := maximum_pulse_rate_is_half_bandwidth
    setup hphysical hfigure hlaws TimeUnit.seconds
  change pulseRateInPulsesPerSecond setup.maximumPulseTransmissionRate =
    frequencyReadout TimeUnit.seconds setup.systemBandwidth / 2 at hrate
  rw [hBandwidthUnits] at hrate
  norm_num at hrate
  constructor
  · exact hrate
  · simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      displayedPulseRateInPulsesPerSecond] using hrate

end PhyXMiniProblems.ProblemPhyXMini0504
