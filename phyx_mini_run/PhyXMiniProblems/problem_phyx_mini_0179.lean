import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0179

open Dimension

/-!
# Speed of sound from a standing wave in an open tube

The primary figure shows longitudinal molecular motion in an `80 cm` tube
containing an unspecified gas.  The driving frequency is `500 Hz`.  Molecular
motion has antinodes at the two open ends and at the midpoint, while the
quarter points are nodes.  Consequently the displayed mode contains two
half-wavelength segments, or one complete wavelength, across the tube.

Length, frequency, and speed are represented by unit-independent Physlib
quantities.  Real numbers are used only for readouts in explicitly named
units, finite mode counts, positions normalized by the tube length, and the
displayed multiple-choice values.  In particular, wavelength and sound speed
are independent setup fields related to the observations only by the
governing standing-wave and propagation laws below.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length as a scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed in a selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Centimeter readout used by the dimension arrow in the figure. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Meter readout used in the SI wave-speed calculation. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Meter-per-second readout of the sound propagation speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- The gas is physically present but is not identified by the problem. -/
inductive AcousticMedium where
  | unknownGas
  deriving DecidableEq, Repr

/-- The two axial ends of the horizontal tube. -/
inductive TubeEndpoint where
  | left
  | right
  deriving DecidableEq, Repr

/-- Acoustic boundary behavior relevant to longitudinal displacement. -/
inductive AcousticBoundaryCondition where
  | openEnd
  | closedEnd
  deriving DecidableEq, Repr

/-- Qualitative kind of disturbance represented by the molecule arrows. -/
inductive AcousticWaveKind where
  | longitudinalStandingSoundWave
  | travelingSoundWave
  deriving DecidableEq, Repr

/-- Five equally spaced axial locations distinguished in the bitmap. -/
inductive TubePointLabel where
  | leftEnd
  | firstQuarter
  | midpoint
  | thirdQuarter
  | rightEnd
  deriving DecidableEq, Repr

/-- Displacement-amplitude role of a point in the standing mode. -/
inductive DisplacementRole where
  | node
  | antinode
  deriving DecidableEq, Repr

/-- Whether the picture draws opposed horizontal arrows at a molecule pair. -/
inductive MoleculeMotionMark where
  | noArrow
  | opposedHorizontalArrows
  deriving DecidableEq, Repr

/-!
Figure-derived geometry and molecule-motion annotations.  Positions are
physical axial distances from the left end, not dimensionless placeholders.
-/
structure StandingSoundWaveFigure where
  positionFromLeft : TubePointLabel → LengthQuantity
  displacementRole : TubePointLabel → DisplacementRole
  moleculeMotionMark : TubePointLabel → MoleculeMotionMark

/-!
Physical quantities and qualitative data for the unknown-gas experiment.
The wavelength and sound speed are deliberately independent fields: neither
is assigned its requested numerical value in this setup structure.
-/
structure OpenTubeAcousticSetup where
  medium : AcousticMedium
  boundaryCondition : TubeEndpoint → AcousticBoundaryCondition
  waveKind : AcousticWaveKind
  tubeLength : LengthQuantity
  wavelength : LengthQuantity
  drivingFrequency : FrequencyQuantity
  soundSpeed : SpeedQuantity
  visibleHalfWavelengthSegmentCount : ℕ
  figure : StandingSoundWaveFigure

/-!
Data read directly from the problem statement and primary figure.  The tube
is open at both ends, its dimension arrow reads `80 cm`, and the frequency
label reads `500 Hz`.  Arrows occur at the endpoint and midpoint antinodes;
the quarter-point molecule pairs have no arrows and are displacement nodes.

The five axial positions only record the evenly spaced molecule columns in
the figure.  No wavelength or sound-speed value occurs in this predicate.
-/
structure MatchesSuppliedOpenTubeFigure
    (setup : OpenTubeAcousticSetup) : Prop where
  mediumIsUnknownGas : setup.medium = .unknownGas
  waveIsLongitudinalStandingSound :
    setup.waveKind = .longitudinalStandingSoundWave
  leftEndIsOpen : setup.boundaryCondition .left = .openEnd
  rightEndIsOpen : setup.boundaryCondition .right = .openEnd
  tubeLengthCentimeters : lengthInCentimeters setup.tubeLength = 80
  frequencyHertz : frequencyInHertz setup.drivingFrequency = 500
  visibleHalfWavelengthSegments :
    setup.visibleHalfWavelengthSegmentCount = 2
  leftEndRole : setup.figure.displacementRole .leftEnd = .antinode
  firstQuarterRole : setup.figure.displacementRole .firstQuarter = .node
  midpointRole : setup.figure.displacementRole .midpoint = .antinode
  thirdQuarterRole : setup.figure.displacementRole .thirdQuarter = .node
  rightEndRole : setup.figure.displacementRole .rightEnd = .antinode
  leftEndMotion :
    setup.figure.moleculeMotionMark .leftEnd = .opposedHorizontalArrows
  firstQuarterNoMotionMark :
    setup.figure.moleculeMotionMark .firstQuarter = .noArrow
  midpointMotion :
    setup.figure.moleculeMotionMark .midpoint = .opposedHorizontalArrows
  thirdQuarterNoMotionMark :
    setup.figure.moleculeMotionMark .thirdQuarter = .noArrow
  rightEndMotion :
    setup.figure.moleculeMotionMark .rightEnd = .opposedHorizontalArrows
  leftEndPosition :
    lengthInCentimeters (setup.figure.positionFromLeft .leftEnd) = 0
  firstQuarterPosition :
    4 * lengthInCentimeters
        (setup.figure.positionFromLeft .firstQuarter) =
      lengthInCentimeters setup.tubeLength
  midpointPosition :
    2 * lengthInCentimeters (setup.figure.positionFromLeft .midpoint) =
      lengthInCentimeters setup.tubeLength
  thirdQuarterPosition :
    4 * lengthInCentimeters
        (setup.figure.positionFromLeft .thirdQuarter) =
      3 * lengthInCentimeters setup.tubeLength
  rightEndPosition :
    lengthInCentimeters (setup.figure.positionFromLeft .rightEnd) =
      lengthInCentimeters setup.tubeLength

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalAcousticParameters
    (setup : OpenTubeAcousticSetup) : Prop where
  tubeLengthPositive : 0 < lengthInMeters setup.tubeLength
  wavelengthPositive : 0 < lengthInMeters setup.wavelength
  frequencyPositive : 0 < frequencyInHertz setup.drivingFrequency
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeed
  segmentCountPositive : 0 < setup.visibleHalfWavelengthSegmentCount

/-!
Governing laws for the pictured nondispersive acoustic standing wave.

* In an open-open tube, each interval between adjacent displacement
  antinodes is one half-wavelength, so `2 L = n lambda` for the visible count
  `n` of such intervals.
* Sound propagation obeys `v = f lambda` in compatible selected units.

These relations contain neither the inferred `0.8 m` wavelength nor the
requested `400 m/s` sound speed.
-/
structure SatisfiesOpenTubeStandingWaveLaws
    (setup : OpenTubeAcousticSetup) : Prop where
  openTubeHarmonicGeometry :
    ∀ unit : LengthUnit,
      2 * lengthReadout unit setup.tubeLength =
        (setup.visibleHalfWavelengthSegmentCount : ℝ) *
          lengthReadout unit setup.wavelength
  soundSpeedEqualsFrequencyTimesWavelength :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeed =
        frequencyReadout timeUnit setup.drivingFrequency *
          lengthReadout lengthUnit setup.wavelength

/-!
Converting the `80 cm` dimension arrow to SI units gives a tube length of
`4/5 m`.  This is a unit-conversion consequence of the figure readout, not a
sound-speed assumption.
-/
lemma tubeLengthInMeters_eq_fourFifths
    (setup : OpenTubeAcousticSetup)
    (h_figure : MatchesSuppliedOpenTubeFigure setup) :
    lengthInMeters setup.tubeLength = 4 / 5 := by
  have length_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun x : NNReal => (x : ℝ)) <|
      congrArg WithDim.val <|
        length.2 UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.centimeters}
    change
      lengthInCentimeters length =
        _ * lengthInMeters length at h
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      WithDim.smul_val, NNReal.smul_def, smul_eq_mul] at h ⊢
    exact h
  have h_length := h_figure.tubeLengthCentimeters
  rw [length_centimeters_eq] at h_length
  norm_num at h_length ⊢
  linarith

/-!
The three displacement antinodes delimit two half-wavelength segments across
the tube.  The open-tube harmonic geometry therefore makes the wavelength
equal to the `0.8 m` tube length.
-/
lemma picturedMode_wavelengthInMeters_eq_fourFifths
    (setup : OpenTubeAcousticSetup)
    (h_figure : MatchesSuppliedOpenTubeFigure setup)
    (h_wave_laws : SatisfiesOpenTubeStandingWaveLaws setup) :
    lengthInMeters setup.wavelength = 4 / 5 := by
  have h_length :=
    tubeLengthInMeters_eq_fourFifths setup h_figure
  have h_geometry :=
    h_wave_laws.openTubeHarmonicGeometry LengthUnit.meters
  change
    2 * lengthInMeters setup.tubeLength =
      (setup.visibleHalfWavelengthSegmentCount : ℝ) *
        lengthInMeters setup.wavelength at h_geometry
  rw [h_length, h_figure.visibleHalfWavelengthSegments] at h_geometry
  norm_num at h_geometry ⊢
  linarith

/-- Labels of the four sound-speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed speed beside an answer label, in meters per second. -/
def displayedAnswerSpeedMetersPerSecond : AnswerChoice → ℝ
  | .A => 600
  | .B => 200
  | .C => 160
  | .D => 400

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed answer agrees with the modeled physical sound speed. -/
def AgreesWithDisplayedSpeedChoice
    (setup : OpenTubeAcousticSetup) (choice : AnswerChoice) : Prop :=
  speedInMetersPerSecond setup.soundSpeed =
    displayedAnswerSpeedMetersPerSecond choice

/-!
At `500 Hz`, the one-wavelength-long `0.8 m` tube gives
`v = f lambda = 400 m/s`.  Thus displayed choice D is correct.

This formalizes `thm:physics:phyx_mini_0179:target`.
-/
theorem problem_phyx_mini_0179
    (setup : OpenTubeAcousticSetup)
    (h_figure : MatchesSuppliedOpenTubeFigure setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_wave_laws : SatisfiesOpenTubeStandingWaveLaws setup) :
    speedInMetersPerSecond setup.soundSpeed = 400 ∧
      AgreesWithDisplayedSpeedChoice setup .D := by
  have h_wavelength :=
    picturedMode_wavelengthInMeters_eq_fourFifths setup h_figure h_wave_laws
  have h_speed :=
    h_wave_laws.soundSpeedEqualsFrequencyTimesWavelength
      LengthUnit.meters TimeUnit.seconds
  change
    speedInMetersPerSecond setup.soundSpeed =
      frequencyInHertz setup.drivingFrequency *
        lengthInMeters setup.wavelength at h_speed
  rw [h_figure.frequencyHertz, h_wavelength] at h_speed
  norm_num at h_speed
  constructor
  · exact h_speed
  · simpa [AgreesWithDisplayedSpeedChoice,
      displayedAnswerSpeedMetersPerSecond] using h_speed

end PhyXMiniProblems.ProblemPhyXMini0179
