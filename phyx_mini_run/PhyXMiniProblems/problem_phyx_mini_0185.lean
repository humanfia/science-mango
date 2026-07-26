import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0185

open Dimension

/-!
# Fundamental longitudinal frequency of an aluminum rod

A long, thin aluminum rod supports a longitudinal standing wave.  Its free
ends are displacement antinodes, so the mode geometry is the same as for an
open--open acoustic tube.  The primary figure also depicts a displacement
node at the center of the rod and opposed axial-motion arrows.

Length, frequency, and longitudinal wave speed are represented by
unit-independent Physlib quantities.  Real numbers below occur only as
readouts in explicitly named units and as displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed, carrying length-per-time dimension. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Kilohertz readout, obtained from the hertz readout by scalar conversion. -/
def frequencyInKilohertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyInHertz frequency / 1000

/-- Meter-per-second readout of the longitudinal wave speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical roles and primary-figure labels -/

/-- Material named by the problem and by the label above the pictured rod. -/
inductive RodMaterial where
  | aluminum
  deriving DecidableEq, Repr

/-- Geometric idealization of the rod used by the longitudinal-wave model. -/
inductive RodGeometry where
  | longThin
  deriving DecidableEq, Repr

/-- How the demonstration excites the longitudinal oscillation. -/
inductive ExcitationMethod where
  | strokingWithVeryDryFingers
  deriving DecidableEq, Repr

/-- Type of disturbance represented by the opposed arrows in the figure. -/
inductive RodWaveKind where
  | longitudinalStandingWave
  | travelingWave
  deriving DecidableEq, Repr

/-- Acoustic boundary model stated to be equivalent to the rod mode. -/
inductive AcousticBoundaryAnalogy where
  | openOpenTube
  | closedClosedTube
  deriving DecidableEq, Repr

/-- Mechanical boundary condition at either end of the rod. -/
inductive RodBoundaryCondition where
  | free
  | clamped
  deriving DecidableEq, Repr

/-- The two mechanical endpoints of the rod. -/
inductive RodEndpoint where
  | left
  | right
  deriving DecidableEq, Repr

/-- Distinguished axial locations visible in the primary figure. -/
inductive RodFigurePoint where
  | leftEnd
  | center
  | rightEnd
  deriving DecidableEq, Repr

/-- Displacement behavior of the standing wave at a distinguished point. -/
inductive DisplacementFeature where
  | node
  | antinode
  deriving DecidableEq, Repr

/-- The text label printed above the rod in the primary figure. -/
inductive RodFigureLabel where
  | aluminumRod
  deriving DecidableEq, Repr

/-- The two axial directions indicated by the blue figure arrows. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-!
Independent physical quantities and qualitative labels in the setup.
`modeNumber = 1` denotes the requested fundamental open--open mode.  Neither
the wavelength nor the frequency is assigned a numerical value here.
-/
structure AluminumRodStandingWaveSetup where
  material : RodMaterial
  geometry : RodGeometry
  excitation : ExcitationMethod
  waveKind : RodWaveKind
  acousticBoundaryAnalogy : AcousticBoundaryAnalogy
  boundaryCondition : RodEndpoint → RodBoundaryCondition
  displacementFeature : RodFigurePoint → DisplacementFeature
  figureLabel : RodFigureLabel
  figureShowsArrowDirection : AxialDirection → Bool
  visibleBlackMarkerCount : ℕ
  rodLength : LengthQuantity
  modeNumber : ℕ
  fundamentalWavelength : LengthQuantity
  fundamentalFrequency : FrequencyQuantity
  longitudinalWaveSpeed : SpeedQuantity

/-!
Problem-statement and primary-figure data.  The two ends are free mechanical
boundaries and displacement antinodes, while the center is a displacement
node.  The five black markers and left/right arrows record the remaining
visible figure features.  No wavelength or frequency answer occurs here.
-/
structure MatchesProblemAndFigureReadouts
    (setup : AluminumRodStandingWaveSetup) : Prop where
  materialIsAluminum : setup.material = .aluminum
  rodIsLongAndThin : setup.geometry = .longThin
  excitationByDryFingers : setup.excitation = .strokingWithVeryDryFingers
  waveIsLongitudinalStanding : setup.waveKind = .longitudinalStandingWave
  equivalentToOpenOpenTube :
    setup.acousticBoundaryAnalogy = .openOpenTube
  leftEndIsFree : setup.boundaryCondition .left = .free
  rightEndIsFree : setup.boundaryCondition .right = .free
  leftEndIsDisplacementAntinode :
    setup.displacementFeature .leftEnd = .antinode
  centerIsDisplacementNode : setup.displacementFeature .center = .node
  rightEndIsDisplacementAntinode :
    setup.displacementFeature .rightEnd = .antinode
  printedFigureLabel : setup.figureLabel = .aluminumRod
  leftArrowIsShown : setup.figureShowsArrowDirection .left = true
  rightArrowIsShown : setup.figureShowsArrowDirection .right = true
  blackMarkerCount : setup.visibleBlackMarkerCount = 5
  rodLengthMeters : lengthInMeters setup.rodLength = 2
  requestedModeIsFundamental : setup.modeNumber = 1

/-! Positivity and nondegeneracy conditions for the physical rod mode. -/
structure HasPhysicalStandingWaveParameters
    (setup : AluminumRodStandingWaveSetup) : Prop where
  rodLengthPositive : 0 < lengthInMeters setup.rodLength
  modeNumberPositive : 0 < setup.modeNumber
  wavelengthPositive : 0 < lengthInMeters setup.fundamentalWavelength
  frequencyPositive : 0 < frequencyInHertz setup.fundamentalFrequency
  waveSpeedPositive :
    0 < speedInMetersPerSecond setup.longitudinalWaveSpeed

/-!
The standard calibrated longitudinal-wave speed used for aluminum in this
problem, expressed as an SI readout.  This is material data, kept separate
from both the figure readouts and the governing wave laws.
-/
structure MatchesStandardAluminumLongitudinalSpeed
    (setup : AluminumRodStandingWaveSetup) : Prop where
  speedMetersPerSecond :
    speedInMetersPerSecond setup.longitudinalWaveSpeed = 6420

/-!
Governing relations for a longitudinal open--open standing-wave mode.

The first field states `2 L = n λ` for mode number `n`; the second is the
propagation relation `v = f λ`.  They are required in every compatible unit
system and do not state the requested wavelength or frequency numerically.
-/
structure SatisfiesLongitudinalStandingWaveLaws
    (setup : AluminumRodStandingWaveSetup) : Prop where
  openOpenModeGeometry :
    ∀ unit : LengthUnit,
      2 * lengthReadout unit setup.rodLength =
        (setup.modeNumber : ℝ) *
          lengthReadout unit setup.fundamentalWavelength
  waveSpeedFrequencyWavelengthRelation :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.longitudinalWaveSpeed =
        frequencyReadout timeUnit setup.fundamentalFrequency *
          lengthReadout lengthUnit setup.fundamentalWavelength

/-! ## Derived values and displayed answer choices -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency printed beside each answer label, in kilohertz. -/
def displayedAnswerFrequencyInKilohertz : AnswerChoice → ℝ
  | .A => 321 / 100
  | .B => 161 / 200
  | .C => 343 / 1000
  | .D => 8 / 5

/-- Place value of the final digit displayed by each kilohertz answer. -/
def displayedPrecisionInKilohertz : AnswerChoice → ℝ
  | .A => 1 / 100
  | .B => 1 / 1000
  | .C => 1 / 1000
  | .D => 1 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a displayed answer to half of its final printed place. -/
def MatchesAnswerChoice
    (setup : AluminumRodStandingWaveSetup) (choice : AnswerChoice) : Prop :=
  |frequencyInKilohertz setup.fundamentalFrequency -
      displayedAnswerFrequencyInKilohertz choice| ≤
    displayedPrecisionInKilohertz choice / 2

/-!
The open--open fundamental geometry and the stated `2.0 m` rod length imply
the intermediate wavelength `λ₁ = 4 m`.
-/
lemma fundamentalWavelengthInMeters_eq_four
    (setup : AluminumRodStandingWaveSetup)
    (_figure : MatchesProblemAndFigureReadouts setup)
    (_laws : SatisfiesLongitudinalStandingWaveLaws setup) :
    lengthInMeters setup.fundamentalWavelength = 4 := by
  have hLength :
      lengthReadout LengthUnit.meters setup.rodLength = 2 := by
    simpa only [lengthInMeters] using _figure.rodLengthMeters
  have hGeometry :=
    _laws.openOpenModeGeometry LengthUnit.meters
  rw [hLength, _figure.requestedModeIsFundamental] at hGeometry
  change lengthReadout LengthUnit.meters setup.fundamentalWavelength = 4
  norm_num at hGeometry ⊢
  linarith

/-!
Combining `λ₁ = 4 m` with the calibrated aluminum speed `6420 m/s` gives the
exact model frequency `f₁ = 1605 Hz`.
-/
lemma fundamentalFrequencyInHertz_eq_1605
    (setup : AluminumRodStandingWaveSetup)
    (_figure : MatchesProblemAndFigureReadouts setup)
    (_materialData : MatchesStandardAluminumLongitudinalSpeed setup)
    (_laws : SatisfiesLongitudinalStandingWaveLaws setup) :
    frequencyInHertz setup.fundamentalFrequency = 1605 := by
  have hWavelength :=
    fundamentalWavelengthInMeters_eq_four setup _figure _laws
  have hSpeed := _materialData.speedMetersPerSecond
  have hWaveRelation :=
    _laws.waveSpeedFrequencyWavelengthRelation
      LengthUnit.meters TimeUnit.seconds
  change lengthReadout LengthUnit.meters setup.fundamentalWavelength = 4 at hWavelength
  change
    speedReadout LengthUnit.meters TimeUnit.seconds
      setup.longitudinalWaveSpeed = 6420 at hSpeed
  rw [hSpeed, hWavelength] at hWaveRelation
  change frequencyReadout TimeUnit.seconds setup.fundamentalFrequency = 1605
  nlinarith

/-!
For the `2.0 m` aluminum rod, the fundamental frequency is `1605 Hz`, which
rounds to `1.6 kHz`, the recorded answer choice D.

This theorem formalizes `thm:physics:phyx_mini_0185:target`.
-/
theorem problem_phyx_mini_0185
    (setup : AluminumRodStandingWaveSetup)
    (_physical : HasPhysicalStandingWaveParameters setup)
    (_figure : MatchesProblemAndFigureReadouts setup)
    (_materialData : MatchesStandardAluminumLongitudinalSpeed setup)
    (_laws : SatisfiesLongitudinalStandingWaveLaws setup) :
    frequencyInHertz setup.fundamentalFrequency = 1605 ∧
      MatchesAnswerChoice setup recordedDatasetAnswer := by
  have hFrequency :=
    fundamentalFrequencyInHertz_eq_1605
      setup _figure _materialData _laws
  constructor
  · exact hFrequency
  · norm_num [MatchesAnswerChoice, recordedDatasetAnswer,
      frequencyInKilohertz, displayedAnswerFrequencyInKilohertz,
      displayedPrecisionInKilohertz, hFrequency]

end PhyXMiniProblems.ProblemPhyXMini0185
