import Mathlib.Topology.Instances.Real.Lemmas
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0307

open Dimension

/-!
# Reflection coefficient from a standing-wave ratio

A continuous traveling wave is incident on a boundary and a smaller,
counter-propagating reflection interferes with it.  The primary image shows a
smooth standing-wave envelope with two arrows labelled `A_max` and a central
arrow labelled `A_min`.

The source does not say whether the wave is mechanical, acoustic, or
electromagnetic.  Its amplitude dimension is therefore an explicit parameter.
Power has its usual watt dimension.  Real numbers below are used only for
coherent SI readouts, dimensionless ratios, figure coordinates, and displayed
percentages.
-/

/-! ## Dimensionful wave quantities and coherent readouts -/

/-- Physical dimension of power: mass times length squared per time cubed. -/
def powerDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent amplitude of a wave of unspecified kind. -/
abbrev WaveAmplitude (amplitudeDimension : Dimension) : Type :=
  Dimensionful (WithDim amplitudeDimension NNReal)

/-- A nonnegative, unit-independent wave power. -/
abbrev WavePower : Type :=
  Dimensionful (WithDim powerDimension NNReal)

/-- A nonnegative, unit-independent propagation speed. -/
abbrev WaveSpeed : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- Coherent SI scalar readout of an amplitude. -/
def amplitudeSIReadout {amplitudeDimension : Dimension}
    (amplitude : WaveAmplitude amplitudeDimension) : ℝ :=
  ((amplitude UnitChoices.SI).val : ℝ)

/-- Watt readout of a wave power. -/
def powerInWatts (power : WavePower) : ℝ :=
  ((power UnitChoices.SI).val : ℝ)

/-- Metres-per-second readout of a propagation speed. -/
def speedInMetersPerSecond (speed : WaveSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Continuous traveling waves and the primary-image labels -/

/-- Horizontal directions used only to distinguish the two propagation senses. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The direction opposite to a given horizontal propagation direction. -/
def oppositeDirection : HorizontalDirection → HorizontalDirection
  | .left => .right
  | .right => .left

/-!
A traveling-wave component.  The dimensionless profile gives its shape as a
function of phase; continuity records the source's description of both the
incident and reflected waves as continuous.  Amplitude and power remain
genuine physical quantities rather than scalar aliases.
-/
structure ContinuousTravelingWave (amplitudeDimension : Dimension) where
  normalizedProfile : ℝ → ℝ
  profileContinuous : Continuous normalizedProfile
  amplitude : WaveAmplitude amplitudeDimension
  averagePower : WavePower
  propagationSpeed : WaveSpeed
  direction : HorizontalDirection

/-- The three vertical amplitude arrows visible in the primary image. -/
inductive FigureArrow where
  | leftMaximum
  | centralMinimum
  | rightMaximum
  deriving DecidableEq, Repr

/-- Text labels printed beside the figure's amplitude arrows. -/
inductive EnvelopeLabel where
  | Amax
  | Amin
  deriving DecidableEq, Repr

/-!
The standing-wave envelope read from the bitmap.  Arrow amplitudes are
physical quantities; no pixel length is interpreted as a calibrated physical
measurement.
-/
structure StandingWaveEnvelopeFigure (amplitudeDimension : Dimension) where
  arrowLabel : FigureArrow → EnvelopeLabel
  arrowAmplitude : FigureArrow → WaveAmplitude amplitudeDimension
  horizontalPositionFromLeftPixels : FigureArrow → ℝ
  showsSmoothEnvelopeCurves : Bool

/-!
The boundary-reflection experiment.  The dimensionless standing-wave ratio
and reflection coefficient are independent measured/model quantities here;
neither is defined from the requested numerical answer.
-/
structure BoundaryReflectionSetup (amplitudeDimension : Dimension) where
  incidentWave : ContinuousTravelingWave amplitudeDimension
  reflectedWave : ContinuousTravelingWave amplitudeDimension
  boundaryPositionMeters : ℝ
  standingWaveRatio : ℝ
  reflectionCoefficient : ℝ
  figure : StandingWaveEnvelopeFigure amplitudeDimension

/-- SI readout of the incident amplitude `A`. -/
def incidentAmplitudeSI {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : ℝ :=
  amplitudeSIReadout setup.incidentWave.amplitude

/-- SI readout of the reflected amplitude `B`. -/
def reflectedAmplitudeSI {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : ℝ :=
  amplitudeSIReadout setup.reflectedWave.amplitude

/-- Figure readout denoted by the left-hand `A_max` label. -/
def maximumEnvelopeAmplitudeSI {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : ℝ :=
  amplitudeSIReadout (setup.figure.arrowAmplitude .leftMaximum)

/-- Figure readout denoted by the central `A_min` label. -/
def minimumEnvelopeAmplitudeSI {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : ℝ :=
  amplitudeSIReadout (setup.figure.arrowAmplitude .centralMinimum)

/-! ## Problem data, physical regime, and governing laws -/

/-!
Direct prose and image evidence.  The two component waves propagate in
opposite directions, the bitmap labels its two outer arrows `A_max` and its
central arrow `A_min`, and the supplied SWR readout is exactly `1.50 = 3/2`.
No reflection coefficient or answer percentage is asserted here.
-/
structure MatchesProblemAndFigureData {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : Prop where
  reflectionTravelsBackThroughIncidentWave :
    setup.reflectedWave.direction =
      oppositeDirection setup.incidentWave.direction
  leftArrowLabel : setup.figure.arrowLabel .leftMaximum = .Amax
  centralArrowLabel : setup.figure.arrowLabel .centralMinimum = .Amin
  rightArrowLabel : setup.figure.arrowLabel .rightMaximum = .Amax
  arrowsOrderedFromLeftToRight :
    setup.figure.horizontalPositionFromLeftPixels .leftMaximum <
        setup.figure.horizontalPositionFromLeftPixels .centralMinimum ∧
      setup.figure.horizontalPositionFromLeftPixels .centralMinimum <
        setup.figure.horizontalPositionFromLeftPixels .rightMaximum
  repeatedMaximumAmplitude :
    amplitudeSIReadout (setup.figure.arrowAmplitude .rightMaximum) =
      maximumEnvelopeAmplitudeSI setup
  smoothEnvelopeShown : setup.figure.showsSmoothEnvelopeCurves = true
  standingWaveRatioReadout : setup.standingWaveRatio = 3 / 2

/-!
Nondegeneracy conditions from the physical scenario.  In particular, the
reflected amplitude `B` is smaller than the positive incident amplitude `A`.
-/
structure HasPhysicalWaveParameters {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : Prop where
  incidentAmplitudePositive : 0 < incidentAmplitudeSI setup
  reflectedAmplitudeSmaller :
    reflectedAmplitudeSI setup < incidentAmplitudeSI setup
  incidentPowerPositive : 0 < powerInWatts setup.incidentWave.averagePower
  reflectedPowerNonnegative :
    0 ≤ powerInWatts setup.reflectedWave.averagePower
  incidentSpeedPositive :
    0 < speedInMetersPerSecond setup.incidentWave.propagationSpeed
  reflectedSpeedPositive :
    0 < speedInMetersPerSecond setup.reflectedWave.propagationSpeed

/-!
Constructive and destructive interference give envelope amplitudes `A + B`
and `A - B`.  Their ratio is the standing-wave ratio.  These are symbolic
governing laws and contain no substituted SWR or requested percentage.
-/
structure SatisfiesStandingWaveInterferenceLaw
    {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : Prop where
  maximumEnvelopeLaw :
    maximumEnvelopeAmplitudeSI setup =
      incidentAmplitudeSI setup + reflectedAmplitudeSI setup
  minimumEnvelopeLaw :
    minimumEnvelopeAmplitudeSI setup =
      incidentAmplitudeSI setup - reflectedAmplitudeSI setup
  standingWaveRatioDefinition :
    setup.standingWaveRatio =
      maximumEnvelopeAmplitudeSI setup /
        minimumEnvelopeAmplitudeSI setup

/-!
Incident and reflected waves in the same medium share a power scale `k`, so
each power is `k` times amplitude squared.  The reflection coefficient is
independently constrained to be reflected power divided by incident power.
This exposes the proportionality invoked by the source without assuming its
numerical consequence.
-/
def SatisfiesCommonMediumPowerReflectionLaw
    {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : Prop :=
  ∃ powerPerAmplitudeSquared : ℝ,
    0 < powerPerAmplitudeSquared ∧
      powerInWatts setup.incidentWave.averagePower =
        powerPerAmplitudeSquared * (incidentAmplitudeSI setup) ^ 2 ∧
      powerInWatts setup.reflectedWave.averagePower =
        powerPerAmplitudeSquared * (reflectedAmplitudeSI setup) ^ 2 ∧
      setup.reflectionCoefficient =
        powerInWatts setup.reflectedWave.averagePower /
          powerInWatts setup.incidentWave.averagePower

/-! ## Displayed percentages and formalization target -/

/-- Labels of the four answer choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Percentage printed beside each multiple-choice label. -/
def displayedReflectionPercentage : AnswerChoice → ℝ
  | .A => 16 / 5
  | .B => 7 / 2
  | .C => 19 / 5
  | .D => 4

/-- Convert a dimensionless power reflection coefficient to percent. -/
def reflectionCoefficientPercentage {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension) : ℝ :=
  100 * setup.reflectionCoefficient

/-- The modeled percentage agrees with one of the displayed choices. -/
def MatchesAnswerChoice {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension)
    (choice : AnswerChoice) : Prop :=
  reflectionCoefficientPercentage setup =
    displayedReflectionPercentage choice

/-- Answer label recorded by the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
An SWR of `3/2`, together with `SWR = (A+B)/(A-B)`, yields the dimensionless
amplitude ratio `B/A = 1/5`.  This is an intermediate derived result, not a
field of any assumption structure.
-/
lemma reflected_to_incident_amplitude_ratio
    {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension)
    (hData : MatchesProblemAndFigureData setup)
    (hPhysical : HasPhysicalWaveParameters setup)
    (hInterference : SatisfiesStandingWaveInterferenceLaw setup) :
    reflectedAmplitudeSI setup / incidentAmplitudeSI setup = 1 / 5 := by
  have hIncidentNe : incidentAmplitudeSI setup ≠ 0 :=
    ne_of_gt hPhysical.incidentAmplitudePositive
  have hDifferenceNe :
      incidentAmplitudeSI setup - reflectedAmplitudeSI setup ≠ 0 :=
    ne_of_gt (sub_pos.mpr hPhysical.reflectedAmplitudeSmaller)
  have hRatio :
      (3 : ℝ) / 2 =
        (incidentAmplitudeSI setup + reflectedAmplitudeSI setup) /
          (incidentAmplitudeSI setup - reflectedAmplitudeSI setup) := by
    calc
      (3 : ℝ) / 2 = setup.standingWaveRatio :=
        hData.standingWaveRatioReadout.symm
      _ = maximumEnvelopeAmplitudeSI setup /
          minimumEnvelopeAmplitudeSI setup :=
        hInterference.standingWaveRatioDefinition
      _ = (incidentAmplitudeSI setup + reflectedAmplitudeSI setup) /
          (incidentAmplitudeSI setup - reflectedAmplitudeSI setup) := by
        rw [hInterference.maximumEnvelopeLaw,
          hInterference.minimumEnvelopeLaw]
  apply (div_eq_iff hIncidentNe).2
  field_simp [hDifferenceNe] at hRatio
  nlinarith

/-!
The common-medium squared-amplitude power law turns the derived amplitude
ratio into the exact power reflection coefficient `R = 1/25`.
-/
lemma reflectionCoefficient_eq_one_twenty_fifth
    {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension)
    (hData : MatchesProblemAndFigureData setup)
    (hPhysical : HasPhysicalWaveParameters setup)
    (hInterference : SatisfiesStandingWaveInterferenceLaw setup)
    (hPower : SatisfiesCommonMediumPowerReflectionLaw setup) :
    setup.reflectionCoefficient = 1 / 25 := by
  obtain ⟨powerPerAmplitudeSquared, hScalePositive, hIncidentPower,
      hReflectedPower, hCoefficient⟩ := hPower
  have hIncidentNe : incidentAmplitudeSI setup ≠ 0 :=
    ne_of_gt hPhysical.incidentAmplitudePositive
  have hAmplitudeRatio :=
    reflected_to_incident_amplitude_ratio setup hData hPhysical hInterference
  have hReflectedAmplitude :
      reflectedAmplitudeSI setup =
        (1 / 5 : ℝ) * incidentAmplitudeSI setup :=
    (div_eq_iff hIncidentNe).mp hAmplitudeRatio
  rw [hCoefficient, hReflectedPower, hIncidentPower, hReflectedAmplitude]
  field_simp [ne_of_gt hScalePositive, hIncidentNe]
  ring

/-!
The exact reflection coefficient is `1/25`; multiplying by `100` gives `4%`.
Thus answer D is the unique displayed match.

This formalizes `thm:physics:phyx_mini_0307:target`.
-/
theorem problem_phyx_mini_0307
    {amplitudeDimension : Dimension}
    (setup : BoundaryReflectionSetup amplitudeDimension)
    (hData : MatchesProblemAndFigureData setup)
    (hPhysical : HasPhysicalWaveParameters setup)
    (hInterference : SatisfiesStandingWaveInterferenceLaw setup)
    (hPower : SatisfiesCommonMediumPowerReflectionLaw setup) :
    setup.reflectionCoefficient = 1 / 25 ∧
      reflectionCoefficientPercentage setup = 4 ∧
      MatchesAnswerChoice setup .D ∧
      (∀ choice, MatchesAnswerChoice setup choice ↔ choice = .D) ∧
      recordedDatasetAnswer = .D := by
  have hCoefficient :=
    reflectionCoefficient_eq_one_twenty_fifth setup hData hPhysical
      hInterference hPower
  refine ⟨hCoefficient, ?_, ?_, ?_, rfl⟩
  · norm_num [reflectionCoefficientPercentage, hCoefficient]
  · norm_num [MatchesAnswerChoice, reflectionCoefficientPercentage,
      displayedReflectionPercentage, hCoefficient]
  · intro choice
    constructor
    · intro hChoice
      cases choice with
      | A =>
          norm_num [MatchesAnswerChoice, reflectionCoefficientPercentage,
            displayedReflectionPercentage, hCoefficient] at hChoice
      | B =>
          norm_num [MatchesAnswerChoice, reflectionCoefficientPercentage,
            displayedReflectionPercentage, hCoefficient] at hChoice
      | C =>
          norm_num [MatchesAnswerChoice, reflectionCoefficientPercentage,
            displayedReflectionPercentage, hCoefficient] at hChoice
      | D => rfl
    · intro hChoice
      subst choice
      norm_num [MatchesAnswerChoice, reflectionCoefficientPercentage,
        displayedReflectionPercentage, hCoefficient]

end PhyXMiniProblems.ProblemPhyXMini0307
