import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0287

open Dimension

/-!
# Amplitude of a sinusoidal string wave from its slope graph

Figure 16-31 plots the dimensionless spatial slope of a traveling sinusoidal
wave at `t = 0`. The horizontal scale is `x_s = 0.80 m`; the graph has
positive slope crests at `0`, `0.40 m`, and `0.80 m`, and its extreme slope
magnitude is `0.20`.

Amplitude, wavelength, tension, and angular frequency are represented by
unit-independent Physlib quantities. Real numbers occur only as readouts in
explicitly named units, dimensionless slopes and phases, and displayed answer
values.
-/

/-- A nonnegative physical length, independent of a selected readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A tensile force, with dimension mass times length per time squared. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative angular frequency, carrying inverse-time dimension. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical length as a real scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read tensile force in the force unit induced by selected base units. -/
def tensionReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (tension : TensionQuantity) : ℝ :=
  ((tension {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read angular frequency in radians per selected time unit. -/
def angularFrequencyReadout
    (timeUnit : TimeUnit) (frequency : AngularFrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Meter readout used on the horizontal figure axis and for amplitudes. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Tension readout in newtons. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  tensionReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds tension

/-- Angular-frequency readout in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  angularFrequencyReadout TimeUnit.seconds frequency

/-- The qualitative wave type stated in the problem. -/
inductive StringWaveKind where
  | sinusoidalTraveling
  | standing
  deriving DecidableEq, Repr

/-- Either possible direction of travel along the string's `x` axis. -/
inductive PropagationDirection where
  | positiveX
  | negativeX
  deriving DecidableEq, Repr

/-- Sign used in the standard traveling-wave phase. -/
def propagationDirectionSign : PropagationDirection → ℝ
  | .positiveX => 1
  | .negativeX => -1

/-- The five successive extrema visible in the supplied slope graph. -/
inductive SlopeGraphExtremum where
  | leftPositiveCrest
  | firstNegativeTrough
  | middlePositiveCrest
  | secondNegativeTrough
  | rightPositiveCrest
  deriving DecidableEq, Repr

/-- Whether a labeled extremum is a positive crest or a negative trough. -/
inductive SlopeExtremumKind where
  | positiveCrest
  | negativeTrough
  deriving DecidableEq, Repr

/-- The alternating extremum kind determined by Figure 16-31. -/
def extremumKind : SlopeGraphExtremum → SlopeExtremumKind
  | .leftPositiveCrest => .positiveCrest
  | .firstNegativeTrough => .negativeTrough
  | .middlePositiveCrest => .positiveCrest
  | .secondNegativeTrough => .negativeTrough
  | .rightPositiveCrest => .positiveCrest

/-!
The primary-image data are retained independently of the modeled wave. The
horizontal coordinates are meter readouts and the vertical values are
dimensionless slopes `dy/dx`.
-/
structure SlopeGraphFigure1631 where
  xScale : LengthQuantity
  xCoordinateInMeters : SlopeGraphExtremum → ℝ
  slopeReadout : SlopeGraphExtremum → ℝ
  showsHorizontalAxisLabelXMeters : Bool
  showsVerticalAxisLabelSlope : Bool
  showsScaleLabelXs : Bool
  showsGrid : Bool

/-!
Independent physical quantities and observable fields of the traveling wave.
Neither the amplitude nor any numerical formula for it is defined from the
figure. Arguments called `xMeters` and `timeSeconds` are coherent-SI scalar
coordinates; the displacement output is a signed meter readout and the
spatial slope is dimensionless.
-/
structure SinusoidalStringWaveSetup where
  waveKind : StringWaveKind
  propagationDirection : PropagationDirection
  amplitude : LengthQuantity
  wavelength : LengthQuantity
  stringTension : TensionQuantity
  angularFrequency : AngularFrequencyQuantity
  waveNumberPerMeter : ℝ
  phaseAtOriginRadians : ℝ
  transverseDisplacementInMeters : ℝ → ℝ → ℝ
  spatialSlope : ℝ → ℝ → ℝ
  maximumSpatialSlopeMagnitude : ℝ
  figure : SlopeGraphFigure1631

/-- Qualitative scenario information from the problem statement. -/
structure MatchesTravelingStringWaveScenario
    (setup : SinusoidalStringWaveSetup) : Prop where
  waveIsSinusoidalAndTraveling : setup.waveKind = .sinusoidalTraveling
  stringIsUnderTension : 0 < tensionInNewtons setup.stringTension

/-- Positivity and nondegeneracy assumptions for the physical model. -/
structure HasPhysicalStringWaveParameters
    (setup : SinusoidalStringWaveSetup) : Prop where
  amplitudePositive : 0 < lengthInMeters setup.amplitude
  wavelengthPositive : 0 < lengthInMeters setup.wavelength
  angularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  waveNumberPositive : 0 < setup.waveNumberPerMeter
  maximumSlopeNonnegative : 0 ≤ setup.maximumSpatialSlopeMagnitude

/-!
General governing laws for a sinusoidal traveling string wave. The
`HasDerivAt` field makes the plotted slope the spatial derivative of the
displacement profile. The relation `S_max = k A` is the standard maximum-slope
law for a sinusoid; it contains neither figure numbers nor the requested
amplitude value.
-/
structure SatisfiesSinusoidalTravelingWaveLaws
    (setup : SinusoidalStringWaveSetup) : Prop where
  waveNumberWavelengthRelation :
    setup.waveNumberPerMeter * lengthInMeters setup.wavelength = 2 * Real.pi
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
  slopeIsSpatialDerivative :
    ∀ xMeters timeSeconds,
      HasDerivAt
        (fun x => setup.transverseDisplacementInMeters x timeSeconds)
        (setup.spatialSlope xMeters timeSeconds) xMeters
  maximumSlopeMagnitudeLaw :
    setup.maximumSpatialSlopeMagnitude =
      setup.waveNumberPerMeter * lengthInMeters setup.amplitude
  slopeMagnitudeBoundAtTimeZero :
    ∀ xMeters,
      |setup.spatialSlope xMeters 0| ≤ setup.maximumSpatialSlopeMagnitude

/-!
Primary-image evidence from Figure 16-31. The graph spans two spatial periods
from `0` to `x_s = 0.80 m`; successive extrema are separated by `0.20 m` and
alternate between slopes `+0.20` and `-0.20`. The wavelength is identified
with the spacing of adjacent positive crests. These are figure/data readouts,
not assumptions about the requested amplitude.
-/
structure MatchesSlopeGraphFigure1631
    (setup : SinusoidalStringWaveSetup) : Prop where
  showsHorizontalAxisLabel :
    setup.figure.showsHorizontalAxisLabelXMeters = true
  showsVerticalAxisLabel : setup.figure.showsVerticalAxisLabelSlope = true
  showsScaleLabel : setup.figure.showsScaleLabelXs = true
  showsGrid : setup.figure.showsGrid = true
  xScaleReadout : lengthInMeters setup.figure.xScale = 4 / 5
  leftCrestPosition :
    setup.figure.xCoordinateInMeters .leftPositiveCrest = 0
  firstTroughPosition :
    setup.figure.xCoordinateInMeters .firstNegativeTrough = 1 / 5
  middleCrestPosition :
    setup.figure.xCoordinateInMeters .middlePositiveCrest = 2 / 5
  secondTroughPosition :
    setup.figure.xCoordinateInMeters .secondNegativeTrough = 3 / 5
  rightCrestPosition :
    setup.figure.xCoordinateInMeters .rightPositiveCrest = 4 / 5
  leftCrestSlope : setup.figure.slopeReadout .leftPositiveCrest = 1 / 5
  firstTroughSlope : setup.figure.slopeReadout .firstNegativeTrough = -(1 / 5)
  middleCrestSlope : setup.figure.slopeReadout .middlePositiveCrest = 1 / 5
  secondTroughSlope : setup.figure.slopeReadout .secondNegativeTrough = -(1 / 5)
  rightCrestSlope : setup.figure.slopeReadout .rightPositiveCrest = 1 / 5
  graphSamplesModeledSlope :
    ∀ point,
      setup.spatialSlope (setup.figure.xCoordinateInMeters point) 0 =
        setup.figure.slopeReadout point
  wavelengthIsAdjacentPositiveCrestSpacing :
    lengthInMeters setup.wavelength =
      setup.figure.xCoordinateInMeters .middlePositiveCrest -
        setup.figure.xCoordinateInMeters .leftPositiveCrest
  maximumSlopeReadFromPositiveCrest :
    setup.maximumSpatialSlopeMagnitude =
      setup.figure.slopeReadout .leftPositiveCrest
  scaleEndsAtRightPositiveCrest :
    setup.figure.xCoordinateInMeters .rightPositiveCrest =
      lengthInMeters setup.figure.xScale

/-- Labels attached to the four amplitude choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Amplitude in meters printed beside each answer label. -/
def displayedAmplitudeInMeters : AnswerChoice → ℝ
  | .A => 89 / 10000
  | .B => 113 / 10000
  | .C => 164 / 10000
  | .D => 127 / 10000

/-- The answer label recorded in the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A displayed four-decimal-meter value matches when the exact amplitude lies
within half of `0.0001 m`, the usual rounding interval.
-/
def RoundsToDisplayedFourDecimalMeters
    (amplitude : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters amplitude - displayedAmplitudeInMeters choice| ≤
    (1 / 20000 : ℝ)

/-- A choice is the unique printed value matching the exact amplitude. -/
def IsUniqueMatchingAnswerChoice
    (setup : SinusoidalStringWaveSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedFourDecimalMeters setup.amplitude choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedFourDecimalMeters setup.amplitude other → other = choice

/-!
From the figure, `lambda = 0.40 m` and `S_max = 0.20`. The sinusoidal laws
give `k lambda = 2 pi` and `S_max = k A`, hence

`A = S_max lambda / (2 pi) = 1 / (25 pi) m`.

This exact value rounds to `0.0127 m`, uniquely selecting answer D. Both the
exact amplitude and the answer selection are conclusions rather than premises.

This formalizes `thm:physics:phyx_mini_0287:target`.
-/
theorem problem_phyx_mini_0287
    (setup : SinusoidalStringWaveSetup)
    (hScenario : MatchesTravelingStringWaveScenario setup)
    (hPhysical : HasPhysicalStringWaveParameters setup)
    (hWaveLaws : SatisfiesSinusoidalTravelingWaveLaws setup)
    (hFigure : MatchesSlopeGraphFigure1631 setup) :
    lengthInMeters setup.amplitude = (1 / 25 : ℝ) / Real.pi ∧
      RoundsToDisplayedFourDecimalMeters setup.amplitude recordedDatasetAnswer ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hWavelength : lengthInMeters setup.wavelength = (2 / 5 : ℝ) := by
    rw [hFigure.wavelengthIsAdjacentPositiveCrestSpacing,
      hFigure.middleCrestPosition, hFigure.leftCrestPosition]
    norm_num
  have hMaximumSlope : setup.maximumSpatialSlopeMagnitude = (1 / 5 : ℝ) := by
    rw [hFigure.maximumSlopeReadFromPositiveCrest, hFigure.leftCrestSlope]
  have hWaveNumber : setup.waveNumberPerMeter = 5 * Real.pi := by
    have hWaveNumberWavelength := hWaveLaws.waveNumberWavelengthRelation
    rw [hWavelength] at hWaveNumberWavelength
    nlinarith [hWaveNumberWavelength]
  have hAmplitudeTimesPi :
      lengthInMeters setup.amplitude * Real.pi = (1 / 25 : ℝ) := by
    have hMaximumSlopeLaw := hWaveLaws.maximumSlopeMagnitudeLaw
    rw [hMaximumSlope, hWaveNumber] at hMaximumSlopeLaw
    nlinarith [hMaximumSlopeLaw]
  have hAmplitude :
      lengthInMeters setup.amplitude = (1 / 25 : ℝ) / Real.pi :=
    (eq_div_iff Real.pi_ne_zero).2 hAmplitudeTimesPi
  have hAmplitudeLower :
      (253 / 20000 : ℝ) ≤ (1 / 25 : ℝ) / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_lt_d2]
  have hAmplitudeUpper :
      (1 / 25 : ℝ) / Real.pi ≤ (255 / 20000 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_d2]
  have hRoundsToD :
      RoundsToDisplayedFourDecimalMeters setup.amplitude recordedDatasetAnswer := by
    rw [RoundsToDisplayedFourDecimalMeters, hAmplitude, abs_le]
    constructor <;>
      simp only [recordedDatasetAnswer, displayedAmplitudeInMeters] <;>
      norm_num at hAmplitudeLower hAmplitudeUpper ⊢ <;>
      linarith
  refine ⟨hAmplitude, hRoundsToD, hRoundsToD, ?_⟩
  intro other hOther
  rw [RoundsToDisplayedFourDecimalMeters, abs_le] at hRoundsToD hOther
  cases other with
  | A =>
      simp only [recordedDatasetAnswer, displayedAmplitudeInMeters] at hRoundsToD hOther
      norm_num at hRoundsToD hOther
      exfalso
      linarith
  | B =>
      simp only [recordedDatasetAnswer, displayedAmplitudeInMeters] at hRoundsToD hOther
      norm_num at hRoundsToD hOther
      exfalso
      linarith
  | C =>
      simp only [recordedDatasetAnswer, displayedAmplitudeInMeters] at hRoundsToD hOther
      norm_num at hRoundsToD hOther
      exfalso
      linarith
  | D =>
      rfl

end PhyXMiniProblems.ProblemPhyXMini0287
