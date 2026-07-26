import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Third-harmonic sound from a four-tube array heard by a receding detector

This file models problem `phyx_mini_0320`.  The primary image labels four
horizontal tubes `1`--`4` and a detector `D` to their right.  Tubes `1` and
`2` are `1.0 m` long, tubes `3` and `4` are `2.0 m` long, and the visible end
caps show that tubes `1` and `3` are closed on the left and open on the right,
whereas tubes `2` and `4` are open at both ends.  Every tube is in its third
harmonic.  Detector `D` moves rightward, directly away from the stationary
tubes.

Lengths, frequencies, positions, and speeds use Physlib's unit-independent
dimensionful quantities.  Scalars below are used only for named-unit
readouts, harmonic numbers, and the dimensionless answer-choice multipliers.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` contains only textual and bitmap readouts;
* `HasPhysicalAcousticParameters` supplies positivity and the subsonic branch;
* `SatisfiesTubeModeAndDopplerLaws` states the standing-wave, propagation,
  harmonic-frequency, and moving-observer Doppler laws;
* `DetectorHearsTube4Fundamental` is the requested tuning condition; and
* `tube4_fundamental_iff_detectorSpeed_twoThirds` derives the required speed
  and identifies displayed choice D.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0320

open Dimension

/-! ## Dimensionful acoustic quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the chosen unit system. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed axial position along the horizontal direction in the image. -/
abbrev AxialPosition : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical acoustic frequency. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical speed with dimension length per time. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a signed axial position in a selected length unit. -/
def positionReadout (unit : LengthUnit) (position : AxialPosition) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Metre readout of a signed axial position. -/
def positionInMeters (position : AxialPosition) : ℝ :=
  positionReadout LengthUnit.meters position

/-- Read a physical frequency in inverse units of a selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Read a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Metres-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical roles and primary-figure labels -/

/-- Tube numbers printed down the left side of the primary image. -/
inductive TubeLabel where
  | tube1
  | tube2
  | tube3
  | tube4
  deriving DecidableEq, Repr

/-- The two axial endpoints of any horizontal tube. -/
inductive TubeEndpoint where
  | left
  | right
  deriving DecidableEq, Repr

/-- Acoustic boundary behavior indicated by the presence or absence of an end cap. -/
inductive AcousticBoundaryCondition where
  | openEnd
  | closedEnd
  deriving DecidableEq, Repr

/-- Motion state of a tube relative to the acoustic medium. -/
inductive TubeMotion where
  | stationaryRelativeToMedium
  deriving DecidableEq, Repr

/-- The two directions along the horizontal axis of the image. -/
inductive AxialDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The detector label printed beneath the blue circular detector. -/
inductive DetectorLabel where
  | D
  deriving DecidableEq, Repr

/-- The unspecified common gas in and around the four tubes. -/
inductive AcousticMedium where
  | gasInAndAroundTubes
  deriving DecidableEq, Repr

/-- Physical geometry and motion data associated with one pictured tube. -/
structure AcousticTube where
  length : LengthQuantity
  boundaryCondition : TubeEndpoint → AcousticBoundaryCondition
  rightEndPosition : AxialPosition
  motionRelativeToMedium : TubeMotion

/-- Physical state of the moving detector `D`. -/
structure DetectorState where
  label : DetectorLabel
  axialPosition : AxialPosition
  motionDirection : AxialDirection
  speedRelativeToMedium : SpeedQuantity

/-!
The independent physical quantities in the four-tube experiment.

The emitted and detected frequencies, fundamental frequencies, wavelengths,
sound speed, and detector speed are independent fields.  In particular, the
setup does not assign the detector speed a multiple of the sound speed.
-/
structure FourTubeDopplerSetup where
  medium : AcousticMedium
  tube : TubeLabel → AcousticTube
  detector : DetectorState
  soundSpeedInMedium : SpeedQuantity
  soundPropagationDirection : TubeLabel → AxialDirection
  excitedHarmonic : TubeLabel → ℕ
  excitedWavelength : TubeLabel → LengthQuantity
  fundamentalFrequency : TubeLabel → FrequencyQuantity
  emittedFrequency : TubeLabel → FrequencyQuantity
  detectedFrequency : TubeLabel → FrequencyQuantity

/-!
Textual data and readouts from the primary image.  The tube lengths and end
conditions record all four depicted tubes even though only tube 4 enters the
final calculation.  Every right tube end lies to the left of detector `D`,
the sound and detector move rightward, and the tubes are stationary; hence
the detector moves directly away from each source.

No detector-speed multiplier or detected-frequency tuning condition occurs
in this structure.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : FourTubeDopplerSetup) : Prop where
  mediumIsCommonGas : setup.medium = .gasInAndAroundTubes
  tube1LengthMeters : lengthInMeters (setup.tube .tube1).length = 1
  tube2LengthMeters : lengthInMeters (setup.tube .tube2).length = 1
  tube3LengthMeters : lengthInMeters (setup.tube .tube3).length = 2
  tube4LengthMeters : lengthInMeters (setup.tube .tube4).length = 2
  tube1LeftClosed :
    (setup.tube .tube1).boundaryCondition .left = .closedEnd
  tube1RightOpen :
    (setup.tube .tube1).boundaryCondition .right = .openEnd
  tube2LeftOpen :
    (setup.tube .tube2).boundaryCondition .left = .openEnd
  tube2RightOpen :
    (setup.tube .tube2).boundaryCondition .right = .openEnd
  tube3LeftClosed :
    (setup.tube .tube3).boundaryCondition .left = .closedEnd
  tube3RightOpen :
    (setup.tube .tube3).boundaryCondition .right = .openEnd
  tube4LeftOpen :
    (setup.tube .tube4).boundaryCondition .left = .openEnd
  tube4RightOpen :
    (setup.tube .tube4).boundaryCondition .right = .openEnd
  detectorIsD : setup.detector.label = .D
  detectorIsRightOfEveryTube :
    ∀ tube,
      positionInMeters (setup.tube tube).rightEndPosition <
        positionInMeters setup.detector.axialPosition
  everyTubeIsStationary :
    ∀ tube,
      (setup.tube tube).motionRelativeToMedium =
        .stationaryRelativeToMedium
  soundTravelsRightward :
    ∀ tube, setup.soundPropagationDirection tube = .right
  detectorMovesRightward : setup.detector.motionDirection = .right
  everyTubeIsInThirdHarmonic :
    ∀ tube, setup.excitedHarmonic tube = 3

/-- Positivity and subsonic conditions selecting the ordinary acoustic branch. -/
structure HasPhysicalAcousticParameters
    (setup : FourTubeDopplerSetup) : Prop where
  tubeLengthPositive :
    ∀ tube, 0 < lengthInMeters (setup.tube tube).length
  wavelengthPositive :
    ∀ tube, 0 < lengthInMeters (setup.excitedWavelength tube)
  fundamentalFrequencyPositive :
    ∀ tube, 0 < frequencyInHertz (setup.fundamentalFrequency tube)
  emittedFrequencyPositive :
    ∀ tube, 0 < frequencyInHertz (setup.emittedFrequency tube)
  detectedFrequencyPositive :
    ∀ tube, 0 < frequencyInHertz (setup.detectedFrequency tube)
  soundSpeedPositive :
    0 < speedInMetersPerSecond setup.soundSpeedInMedium
  detectorSpeedPositive :
    0 < speedInMetersPerSecond setup.detector.speedRelativeToMedium
  detectorIsSubsonic :
    speedInMetersPerSecond setup.detector.speedRelativeToMedium <
      speedInMetersPerSecond setup.soundSpeedInMedium
  harmonicNumberPositive : ∀ tube, 0 < setup.excitedHarmonic tube

/-!
Governing relations for the standing modes and the sound heard by `D`.

* An open--open mode obeys `2 L = n λ`.
* A mode with exactly one closed end obeys `4 L = n λ`, with odd `n`.
* A harmonic's emitted frequency is `n` times its fundamental frequency.
* Sound propagation obeys `v = f λ`.
* For a stationary source and a subsonic observer receding in the direction
  of propagation, the detected frequency is `f (v-u)/v`.

The laws are stated in arbitrary compatible units.  None asserts the
requested value `u = 2v/3` or that tube 4 is heard at its fundamental.
-/
structure SatisfiesTubeModeAndDopplerLaws
    (setup : FourTubeDopplerSetup) : Prop where
  openOpenModeGeometry :
    ∀ (tube : TubeLabel) (unit : LengthUnit),
      (setup.tube tube).boundaryCondition .left = .openEnd →
      (setup.tube tube).boundaryCondition .right = .openEnd →
      2 * lengthReadout unit (setup.tube tube).length =
        (setup.excitedHarmonic tube : ℝ) *
          lengthReadout unit (setup.excitedWavelength tube)
  oneClosedModeGeometry :
    ∀ (tube : TubeLabel) (unit : LengthUnit),
      (((setup.tube tube).boundaryCondition .left = .closedEnd ∧
          (setup.tube tube).boundaryCondition .right = .openEnd) ∨
        ((setup.tube tube).boundaryCondition .left = .openEnd ∧
          (setup.tube tube).boundaryCondition .right = .closedEnd)) →
      4 * lengthReadout unit (setup.tube tube).length =
        (setup.excitedHarmonic tube : ℝ) *
          lengthReadout unit (setup.excitedWavelength tube)
  oneClosedModeHasOddHarmonicNumber :
    ∀ tube : TubeLabel,
      (((setup.tube tube).boundaryCondition .left = .closedEnd ∧
          (setup.tube tube).boundaryCondition .right = .openEnd) ∨
        ((setup.tube tube).boundaryCondition .left = .openEnd ∧
          (setup.tube tube).boundaryCondition .right = .closedEnd)) →
      setup.excitedHarmonic tube % 2 = 1
  harmonicFrequencyRatio :
    ∀ (tube : TubeLabel) (unit : TimeUnit),
      frequencyReadout unit (setup.emittedFrequency tube) =
        (setup.excitedHarmonic tube : ℝ) *
          frequencyReadout unit (setup.fundamentalFrequency tube)
  soundSpeedEqualsFrequencyTimesWavelength :
    ∀ (tube : TubeLabel) (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeedInMedium =
        frequencyReadout timeUnit (setup.emittedFrequency tube) *
          lengthReadout lengthUnit (setup.excitedWavelength tube)
  recedingDetectorDopplerLaw :
    ∀ (tube : TubeLabel) (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      (setup.tube tube).motionRelativeToMedium =
          .stationaryRelativeToMedium →
      positionReadout lengthUnit (setup.tube tube).rightEndPosition <
          positionReadout lengthUnit setup.detector.axialPosition →
      setup.soundPropagationDirection tube = .right →
      setup.detector.motionDirection = .right →
      frequencyReadout timeUnit (setup.detectedFrequency tube) =
        frequencyReadout timeUnit (setup.emittedFrequency tube) *
          (speedReadout lengthUnit timeUnit setup.soundSpeedInMedium -
            speedReadout lengthUnit timeUnit
              setup.detector.speedRelativeToMedium) /
          speedReadout lengthUnit timeUnit setup.soundSpeedInMedium

/-! ## Requested tuning condition and displayed answer choices -/

/-!
The condition in the question: the sound from tube 4 is detected at tube 4's
fundamental frequency.  This is a proposition about two independent physical
frequency fields, not a definition of either frequency or of detector speed.
-/
def DetectorHearsTube4Fundamental
    (setup : FourTubeDopplerSetup) : Prop :=
  setup.detectedFrequency .tube4 = setup.fundamentalFrequency .tube4

/-- Labels of the four displayed speed choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless multiplier of the sound speed printed beside each choice. -/
def AnswerChoice.soundSpeedMultiplier : AnswerChoice → NNReal
  | .A => 1 / 2
  | .B => 2 / 5
  | .C => 1 / 3
  | .D => 2 / 3

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice agrees with the detector's physical speed. -/
def DetectorSpeedAgreesWithChoice
    (setup : FourTubeDopplerSetup) (choice : AnswerChoice) : Prop :=
  setup.detector.speedRelativeToMedium =
    choice.soundSpeedMultiplier • setup.soundSpeedInMedium

/-!
For tube 4's third harmonic, the receding-observer Doppler factor must be
`1/3` in order for the detected frequency to equal the fundamental.  Hence
detector `D` must move at `2/3` of the sound speed, exactly displayed choice D.

The equivalence keeps the tuning condition and the requested speed on the
conclusion side; neither is a hypothesis or a governing-law field.

This formalizes `thm:physics:phyx_mini_0320:target`.
-/
theorem tube4_fundamental_iff_detectorSpeed_twoThirds
    (setup : FourTubeDopplerSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_laws : SatisfiesTubeModeAndDopplerLaws setup) :
    DetectorHearsTube4Fundamental setup ↔
      (setup.detector.speedRelativeToMedium =
          (2 / 3 : NNReal) • setup.soundSpeedInMedium ∧
        DetectorSpeedAgreesWithChoice setup recordedDatasetAnswer) := by
  let speedUnits : UnitChoices :=
    { UnitChoices.SI with
      length := LengthUnit.meters, time := TimeUnit.seconds }
  let frequencyUnits : UnitChoices :=
    { UnitChoices.SI with time := TimeUnit.seconds }
  have h_sound_pos :
      0 < speedReadout LengthUnit.meters TimeUnit.seconds
        setup.soundSpeedInMedium :=
    h_physical.soundSpeedPositive
  have h_fundamental_pos :
      0 < frequencyReadout TimeUnit.seconds
        (setup.fundamentalFrequency .tube4) :=
    h_physical.fundamentalFrequencyPositive .tube4
  have h_harmonic :=
    h_laws.harmonicFrequencyRatio .tube4 TimeUnit.seconds
  rw [h_figure.everyTubeIsInThirdHarmonic .tube4] at h_harmonic
  norm_num at h_harmonic
  have h_doppler :=
    h_laws.recedingDetectorDopplerLaw .tube4
      LengthUnit.meters TimeUnit.seconds
      (h_figure.everyTubeIsStationary .tube4)
      (by
        simpa [positionInMeters] using
          h_figure.detectorIsRightOfEveryTube .tube4)
      (h_figure.soundTravelsRightward .tube4)
      h_figure.detectorMovesRightward
  constructor
  · intro h_tuning
    have h_detected_eq_fundamental :
        frequencyReadout TimeUnit.seconds
            (setup.detectedFrequency .tube4) =
          frequencyReadout TimeUnit.seconds
            (setup.fundamentalFrequency .tube4) := by
      exact congrArg (frequencyReadout TimeUnit.seconds) h_tuning
    have h_speed_readout :
        speedReadout LengthUnit.meters TimeUnit.seconds
            setup.detector.speedRelativeToMedium =
          (2 / 3 : ℝ) *
            speedReadout LengthUnit.meters TimeUnit.seconds
              setup.soundSpeedInMedium := by
      rw [h_detected_eq_fundamental, h_harmonic] at h_doppler
      field_simp [ne_of_gt h_sound_pos] at h_doppler
      nlinarith
    have h_speed :
        setup.detector.speedRelativeToMedium =
          (2 / 3 : NNReal) • setup.soundSpeedInMedium := by
      have h_speed_at_base :
          setup.detector.speedRelativeToMedium speedUnits =
            ((2 / 3 : NNReal) • setup.soundSpeedInMedium) speedUnits := by
        apply WithDim.ext
        apply NNReal.eq
        simpa [speedUnits, speedReadout, Dimensionful.smul_apply,
          WithDim.smul_val, NNReal.smul_def] using h_speed_readout
      apply Dimensionful.ext
      funext units
      rw [setup.detector.speedRelativeToMedium.property speedUnits units,
        ((2 / 3 : NNReal) • setup.soundSpeedInMedium).property
          speedUnits units,
        h_speed_at_base]
    refine ⟨h_speed, ?_⟩
    simpa [DetectorSpeedAgreesWithChoice, recordedDatasetAnswer,
      AnswerChoice.soundSpeedMultiplier] using h_speed
  · rintro ⟨h_speed, _h_choice⟩
    have h_speed_readout_congr :=
      congrArg
        (speedReadout LengthUnit.meters TimeUnit.seconds) h_speed
    have h_speed_readout :
        speedReadout LengthUnit.meters TimeUnit.seconds
            setup.detector.speedRelativeToMedium =
          (2 / 3 : ℝ) *
            speedReadout LengthUnit.meters TimeUnit.seconds
              setup.soundSpeedInMedium := by
      simpa [speedReadout, Dimensionful.smul_apply, WithDim.smul_val,
        NNReal.smul_def] using h_speed_readout_congr
    have h_detected_eq_fundamental :
        frequencyReadout TimeUnit.seconds
            (setup.detectedFrequency .tube4) =
          frequencyReadout TimeUnit.seconds
            (setup.fundamentalFrequency .tube4) := by
      rw [h_harmonic, h_speed_readout] at h_doppler
      field_simp [ne_of_gt h_sound_pos] at h_doppler
      nlinarith
    unfold DetectorHearsTube4Fundamental
    have h_frequency_at_base :
        setup.detectedFrequency .tube4 frequencyUnits =
          setup.fundamentalFrequency .tube4 frequencyUnits := by
      apply WithDim.ext
      apply NNReal.eq
      simpa [frequencyUnits, frequencyReadout] using
        h_detected_eq_fundamental
    apply Dimensionful.ext
    funext units
    rw [(setup.detectedFrequency .tube4).property frequencyUnits units,
      (setup.fundamentalFrequency .tube4).property frequencyUnits units,
      h_frequency_at_base]

end PhyXMiniProblems.ProblemPhyXMini0320
