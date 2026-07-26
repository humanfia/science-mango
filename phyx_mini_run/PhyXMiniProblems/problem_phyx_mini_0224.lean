import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0224

open Dimension

/-!
# Fundamental frequency of an alpenhorn

The alpenhorn is modeled as an air-filled tube open at both ends.  Its
fundamental longitudinal mode has wavelength twice the horn length, and its
frequency is related to the speed of sound by `v = λ f`.

Length, frequency, and propagation speed are unit-independent Physlib
quantities.  Real numbers below are only readouts in named units, categorical
figure data, mode numbers, or displayed answer values.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the units used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative propagation speed, carrying length-per-time dimension. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of a selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a physical speed in selected length and time units. -/
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

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical roles and primary-image information -/

/-- The traditional wind instrument named in the source problem. -/
inductive HornKind where
  | alpenhorn
  deriving DecidableEq, Repr

/-- The two enharmonic names given for the popular `3.4 m` horn. -/
inductive HornPitchName where
  | fSharp
  | gFlat
  deriving DecidableEq, Repr

/-- The two ends of the idealized acoustic tube. -/
inductive HornEnd where
  | mouthpiece
  | flaredBell
  deriving DecidableEq, Repr

/-- Acoustic boundary conditions admitted by the tube model. -/
inductive AcousticBoundaryCondition where
  | openEnd
  | closedEnd
  deriving DecidableEq, Repr

/-- The propagation medium inside the horn. -/
inductive AcousticMedium where
  | airInsideHorn
  deriving DecidableEq, Repr

/-- Qualitative horn features visible in the supplied photograph. -/
inductive FigureHornFeature where
  | longBody
  | flaredBellOpening
  | woodenAppearance
  deriving DecidableEq, Repr

/-!
Independent physical quantities and qualitative attributes of the setup.
`modeNumber = 1` denotes the requested fundamental longitudinal mode.  Neither
the wavelength nor the frequency is assigned a numerical value here.
-/
structure AlpenhornResonanceSetup where
  hornKind : HornKind
  pitchNames : HornPitchName → Bool
  hornLength : LengthQuantity
  boundaryCondition : HornEnd → AcousticBoundaryCondition
  medium : AcousticMedium
  modeNumber : ℕ
  fundamentalWavelength : LengthQuantity
  fundamentalFrequency : FrequencyQuantity
  soundSpeed : SpeedQuantity
  onlyOneModeResonatesWhilePlayed : Prop
  figureShowsFeature : FigureHornFeature → Bool
  figureVisibleHornCount : ℕ

/-!
Problem-statement and primary-image readouts.  The prose supplies the horn
length, pitch names, open--open idealization, and requested fundamental mode.
The photograph supplies four visible long wooden horns with flared bell
openings.  No wavelength or frequency answer appears in this structure.
-/
structure MatchesProblemAndFigureReadouts
    (setup : AlpenhornResonanceSetup) : Prop where
  instrumentIsAlpenhorn : setup.hornKind = .alpenhorn
  fSharpNameIsUsed : setup.pitchNames .fSharp = true
  gFlatNameIsUsed : setup.pitchNames .gFlat = true
  hornLengthMeters : lengthInMeters setup.hornLength = 34 / 10
  mouthpieceModeledOpen :
    setup.boundaryCondition .mouthpiece = .openEnd
  bellModeledOpen :
    setup.boundaryCondition .flaredBell = .openEnd
  hornContainsAir : setup.medium = .airInsideHorn
  requestedModeIsFundamental : setup.modeNumber = 1
  singleModeResonance : setup.onlyOneModeResonatesWhilePlayed
  photographShowsLongBodies :
    setup.figureShowsFeature .longBody = true
  photographShowsFlaredBellOpenings :
    setup.figureShowsFeature .flaredBellOpening = true
  photographShowsWoodenAppearance :
    setup.figureShowsFeature .woodenAppearance = true
  photographVisibleHornCount : setup.figureVisibleHornCount = 4

/-! Positivity and nondegeneracy conditions for the acoustic mode. -/
structure HasPhysicalAcousticParameters
    (setup : AlpenhornResonanceSetup) : Prop where
  hornLengthPositive : 0 < lengthInMeters setup.hornLength
  modeNumberPositive : 0 < setup.modeNumber
  wavelengthPositive : 0 < lengthInMeters setup.fundamentalWavelength
  frequencyPositive : 0 < frequencyInHertz setup.fundamentalFrequency
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeed

/-!
Standard room-temperature sound-speed data used to evaluate the acoustic
laws.  It is separate from both the source/figure readouts and the unknown
fundamental frequency.
-/
structure MatchesStandardAirSoundSpeed
    (setup : AlpenhornResonanceSetup) : Prop where
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeed = 343

/-!
Governing relations for an open--open longitudinal standing wave.

The first field states `2 L = n λ`; the second states `v = λ f`.  They are
given in every compatible choice of units and contain no numerical value for
the requested frequency or wavelength.
-/
structure SatisfiesOpenOpenAcousticLaws
    (setup : AlpenhornResonanceSetup) : Prop where
  openOpenModeGeometry :
    ∀ unit : LengthUnit,
      2 * lengthReadout unit setup.hornLength =
        (setup.modeNumber : ℝ) *
          lengthReadout unit setup.fundamentalWavelength
  waveSpeedFrequencyWavelengthRelation :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeed =
        lengthReadout lengthUnit setup.fundamentalWavelength *
          frequencyReadout timeUnit setup.fundamentalFrequency

/-! ## Derived values and displayed answer choices -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Frequency in hertz printed beside each answer label. -/
def displayedAnswerFrequencyInHertz : AnswerChoice → ℝ
  | .A => 62
  | .B => 56
  | .C => 44
  | .D => 50

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Agreement with a whole-hertz displayed answer.  Half a hertz is the natural
tolerance for rounding a model prediction to the nearest displayed hertz.
-/
def MatchesAnswerChoice
    (setup : AlpenhornResonanceSetup) (choice : AnswerChoice) : Prop :=
  |frequencyInHertz setup.fundamentalFrequency -
      displayedAnswerFrequencyInHertz choice| ≤ 1 / 2

/-!
The open--open fundamental geometry and the stated `3.4 m` horn length imply
the intermediate wavelength `λ₁ = 6.8 m`.
-/
lemma fundamentalWavelengthInMeters_eq
    (setup : AlpenhornResonanceSetup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_laws : SatisfiesOpenOpenAcousticLaws setup) :
    lengthInMeters setup.fundamentalWavelength = (34 / 5 : ℝ) := by
  have h := _laws.openOpenModeGeometry LengthUnit.meters
  change 2 * lengthInMeters setup.hornLength =
      (setup.modeNumber : ℝ) *
        lengthInMeters setup.fundamentalWavelength at h
  rw [_readouts.hornLengthMeters, _readouts.requestedModeIsFundamental] at h
  norm_num at h
  linarith

/-!
Combining `λ₁ = 6.8 m` with the calibrated sound speed `343 m/s` gives the
exact model frequency `f₁ = 1715 / 34 Hz`, approximately `50.44 Hz`.
-/
lemma fundamentalFrequencyInHertz_eq
    (setup : AlpenhornResonanceSetup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_airData : MatchesStandardAirSoundSpeed setup)
    (_laws : SatisfiesOpenOpenAcousticLaws setup) :
    frequencyInHertz setup.fundamentalFrequency = (1715 / 34 : ℝ) := by
  have hWavelength :=
    fundamentalWavelengthInMeters_eq setup _readouts _laws
  have hWave := _laws.waveSpeedFrequencyWavelengthRelation
    LengthUnit.meters TimeUnit.seconds
  change speedInMetersPerSecond setup.soundSpeed =
      lengthInMeters setup.fundamentalWavelength *
        frequencyInHertz setup.fundamentalFrequency at hWave
  rw [_airData.soundSpeedMetersPerSecond, hWavelength] at hWave
  norm_num at hWave
  linarith

/-!
The `3.4 m` open--open alpenhorn has model fundamental frequency
`1715 / 34 Hz ≈ 50.44 Hz`, which rounds to the recorded answer D (`50 Hz`).

This formalizes `thm:physics:phyx_mini_0224:target`.
-/
theorem problem_phyx_mini_0224
    (setup : AlpenhornResonanceSetup)
    (_physical : HasPhysicalAcousticParameters setup)
    (_readouts : MatchesProblemAndFigureReadouts setup)
    (_airData : MatchesStandardAirSoundSpeed setup)
    (_laws : SatisfiesOpenOpenAcousticLaws setup) :
    frequencyInHertz setup.fundamentalFrequency = (1715 / 34 : ℝ) ∧
      MatchesAnswerChoice setup recordedDatasetAnswer := by
  have hFrequency :=
    fundamentalFrequencyInHertz_eq setup _readouts _airData _laws
  refine ⟨hFrequency, ?_⟩
  norm_num [MatchesAnswerChoice, recordedDatasetAnswer,
    displayedAnswerFrequencyInHertz, hFrequency, abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0224
