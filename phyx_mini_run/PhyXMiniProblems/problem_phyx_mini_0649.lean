import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0649

open Dimension

/-!
# Maximum rate of a bandwidth-limited rectangular pulse train

The primary figure shows a periodic rectangular pulse train. Each high pulse
has duration `Delta t`, the following low interval has the same duration, and
the start-to-start period is labelled `T = 2 Delta t`. The electronics system
has a bandwidth of `200 kHz`.

Durations, bandwidths, and pulse rates are represented by unit-independent
Physlib quantities. Real numbers below occur only as readouts in named time
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

The maximum rate is an independent inverse-time quantity. Its relation to the
independent period, high- and low-state durations, and bandwidth is imposed
only by the figure data and general laws below; no numerical answer is built
into this structure.
-/
structure BandwidthLimitedPulseTrain where
  figure : PulseTrainFigure
  pulseDuration : DurationQuantity
  lowStateDuration : DurationQuantity
  period : DurationQuantity
  systemBandwidth : FrequencyQuantity
  maximumPulseTransmissionRate : FrequencyQuantity

/-!
Data transcribed from the prose and the primary image: a periodic rectangular
pulse train, horizontal time axis `t`, pulse-width arrow `Delta t`, period
arrow `T = 2 Delta t`, equal high and low intervals, and `200 kHz` electronics
bandwidth.

The displayed period relation is stated in every time unit. No maximum-rate
value or answer choice occurs here.
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
  highAndLowStateDurationsAreEqual : ∀ unit : TimeUnit,
    durationReadout unit setup.lowStateDuration =
      durationReadout unit setup.pulseDuration
  periodIsHighStateFollowedByLowState : ∀ unit : TimeUnit,
    durationReadout unit setup.period =
      durationReadout unit setup.pulseDuration +
        durationReadout unit setup.lowStateDuration
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
  lowStateDurationPositive :
    0 < durationInSeconds setup.lowStateDuration
  periodPositive :
    0 < durationInSeconds setup.period
  bandwidthPositive :
    0 < frequencyInHertz setup.systemBandwidth
  maximumRatePositive :
    0 < pulseRateInPulsesPerSecond setup.maximumPulseTransmissionRate

/-!
The ideal bandwidth-limited resolution model used by the numerical problem.

At the limiting pulse width the reciprocal bandwidth-duration relation is
`B Delta-t = 1`. A periodic train sends one pulse per start-to-start period,
so its limiting pulse rate obeys `R T = 1`. Both laws are expressed in every
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
  | .A => 200000
  | .B => 150000
  | .C => 100000
  | .D => 50000

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A physical maximum pulse rate agrees with the value printed for a choice. -/
def MatchesAnswerChoice
    (setup : BandwidthLimitedPulseTrain) (choice : AnswerChoice) : Prop :=
  pulseRateInPulsesPerSecond setup.maximumPulseTransmissionRate =
    displayedPulseRateInPulsesPerSecond choice

/-!
For an ideal pulse train with `T = 2 Delta-t`, the limiting reciprocal laws
give a maximum rate equal to one half of the system bandwidth. This is a
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
  have hbandwidth :=
    hlaws.limitingBandwidthDurationRelation unit
  have hrate :=
    hlaws.onePulsePerPeriodRelation unit
  have hperiod :=
    hfigure.displayedPeriodRelation unit
  have hpulse_ne :
      durationReadout unit setup.pulseDuration ≠ 0 := by
    intro hpulse_zero
    rw [hpulse_zero, mul_zero] at hbandwidth
    norm_num at hbandwidth
  have hproducts :
      (2 * frequencyReadout unit setup.maximumPulseTransmissionRate) *
          durationReadout unit setup.pulseDuration =
        frequencyReadout unit setup.systemBandwidth *
          durationReadout unit setup.pulseDuration := by
    calc
      (2 * frequencyReadout unit setup.maximumPulseTransmissionRate) *
          durationReadout unit setup.pulseDuration =
          frequencyReadout unit setup.maximumPulseTransmissionRate *
            (2 * durationReadout unit setup.pulseDuration) := by ring
      _ = frequencyReadout unit setup.maximumPulseTransmissionRate *
            durationReadout unit setup.period := by rw [hperiod]
      _ = 1 := hrate
      _ = frequencyReadout unit setup.systemBandwidth *
            durationReadout unit setup.pulseDuration := hbandwidth.symm
  have htwice :
      2 * frequencyReadout unit setup.maximumPulseTransmissionRate =
        frequencyReadout unit setup.systemBandwidth :=
    mul_right_cancel₀ hpulse_ne hproducts
  linarith

/-!
A bandwidth of `200 kHz` therefore permits at most `100 kHz`, or
`1.0 * 10^5 pulses/s`, for the depicted 50%-duty pulse train. This is the
displayed answer C.

This formalizes `thm:physics:phyx_mini_0649:target`.
-/
theorem problem_phyx_mini_0649
    (setup : BandwidthLimitedPulseTrain)
    (hphysical : HasPhysicalPulseTrainParameters setup)
    (hfigure : MatchesProblemStatementAndFigure setup)
    (hlaws : SatisfiesIdealPulseBandwidthLaws setup) :
    pulseRateInPulsesPerSecond setup.maximumPulseTransmissionRate = 100000 ∧
      MatchesAnswerChoice setup recordedDatasetAnswer := by
  have hscale := setup.systemBandwidth.property
    ({UnitChoices.SI with time := TimeUnit.milliseconds})
    ({UnitChoices.SI with time := TimeUnit.seconds})
  have hscale_val := congrArg
    (fun value : WithDim T𝓭⁻¹ NNReal => (value.val : ℝ)) hscale
  have hfrequency_scale :
      ((({UnitChoices.SI with time := TimeUnit.milliseconds} :
            UnitChoices).dimScale
          ({UnitChoices.SI with time := TimeUnit.seconds} : UnitChoices)
          T𝓭⁻¹ : NNReal) : ℝ) = 1000 := by
    rw [UnitChoices.dimScale_of_inv_eq_swap]
    norm_num [UnitChoices.dimScale, TimeUnit.milliseconds, TimeUnit.scale,
      TimeUnit.div_eq_val, TimeUnit.seconds, NNReal.smul_def]
    rfl
  have hbandwidth_hertz :
      frequencyInHertz setup.systemBandwidth =
        1000 * bandwidthInKilohertz setup.systemBandwidth := by
    simp only [WithDim.dim_apply, WithDim.smul_val, smul_eq_mul,
      NNReal.coe_mul] at hscale_val
    rw [hfrequency_scale] at hscale_val
    exact hscale_val
  have hhalf := maximum_pulse_rate_is_half_bandwidth
    setup hphysical hfigure hlaws TimeUnit.seconds
  have hrate :
      pulseRateInPulsesPerSecond setup.maximumPulseTransmissionRate =
        100000 := by
    change frequencyReadout TimeUnit.seconds
      setup.maximumPulseTransmissionRate = 100000
    unfold frequencyInHertz at hbandwidth_hertz
    nlinarith [hhalf, hbandwidth_hertz,
      hfigure.statedSystemBandwidthKilohertz]
  refine ⟨hrate, ?_⟩
  simpa [MatchesAnswerChoice, recordedDatasetAnswer,
    displayedPulseRateInPulsesPerSecond] using hrate

end PhyXMiniProblems.ProblemPhyXMini0649
