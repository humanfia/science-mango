import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0184

open Dimension

/-!
# Tuning-fork frequency from successive resonances of a telescoping tube

The primary image shows an open tube assembled from a fixed `40 cm` section
and a movable `40 cm` insert. A tuning fork is held beside the left opening.
As the insert is pulled out, standing waves are observed at total lengths
`L = 42.5 cm`, `56.7 cm`, and `70.9 cm`; sound travels at `343 m/s`.

Lengths, frequency, and speed are represented by unit-independent Physlib
quantities. Real numbers occur only as readouts in selected units or as the
displayed multiple-choice data. In particular, the fork frequency is an
independent physical quantity related to the observations only by the
governing acoustic laws below.

The listed resonance spacing implies a frequency of approximately `1.208 kHz`,
which conflicts with the recorded option `D = 12.1 kHz`. The formal target
states the physical consequence and makes that source-data mismatch explicit.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical frequency, carrying inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative physical acoustic propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical frequency in inverse units of the selected time unit. -/
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

/-- Centimeter readout used by the problem statement and primary image. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Kilohertz readout used by the displayed answer choices. -/
def frequencyInKilohertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyInHertz frequency / 1000

/-- Meter-per-second readout of the sound speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- The two physical tube pieces whose lengths are marked `40 cm`. -/
inductive TubePart where
  | fixedOuterTube
  | movableInsert
  deriving DecidableEq, Repr

/-- Labels on the three dimension arrows in the primary image. -/
inductive FigureLengthLabel where
  | fixedTubeFortyCentimeters
  | insertFortyCentimeters
  | totalLengthL
  deriving DecidableEq, Repr

/-- The three resonant configurations observed while pulling out the insert. -/
inductive ResonanceObservation where
  | first
  | second
  | third
  deriving DecidableEq, Repr

/-- The two open ends visible in the primary image. -/
inductive TubeEnd where
  | leftByTuningFork
  | rightAtInsert
  deriving DecidableEq, Repr

/-- Acoustic boundary condition at a tube end. -/
inductive AcousticBoundaryCondition where
  | openEnd
  | closedEnd
  deriving DecidableEq, Repr

/-- Motion allowed by the overlapping insert pictured in the figure. -/
inductive InsertMobility where
  | telescopesAlongTubeAxis
  deriving DecidableEq, Repr

/-- Placement of the vibrating acoustic source relative to the tube. -/
inductive TuningForkPlacement where
  | nextToLeftOpenEnd
  deriving DecidableEq, Repr

/-- The propagation medium stipulated by the acoustic scenario. -/
inductive AcousticMedium where
  | airInsideTube
  deriving DecidableEq, Repr

/-!
All independent objects, physical quantities, and observations in the
experiment. `commonEndCorrection` is a configuration-independent offset
between geometric and effective acoustic length; it accommodates the usual
open-end correction and cancels when successive resonances are subtracted.
No field assigns a numerical wavelength or frequency.
-/
structure TelescopingTubeResonanceSetup where
  tubePartLength : TubePart → LengthQuantity
  tubeTotalLengthL : ResonanceObservation → LengthQuantity
  figureMarkedLength :
    ResonanceObservation → FigureLengthLabel → LengthQuantity
  boundaryCondition : TubeEnd → AcousticBoundaryCondition
  insertMobility : InsertMobility
  tuningForkPlacement : TuningForkPlacement
  medium : AcousticMedium
  soundSpeed : SpeedQuantity
  soundWavelength : LengthQuantity
  tuningForkFrequency : FrequencyQuantity
  commonEndCorrection : LengthQuantity
  standingWaveObserved : ResonanceObservation → Prop
  successivePulledOutResonance :
    ResonanceObservation → ResonanceObservation → Prop
  longitudinalModeNumber : ResonanceObservation → ℕ

/-!
Primary-image information: both component arrows are labelled `40 cm`, the
lower arrow is the varying total length `L`, the insert telescopes axially,
and the drawn acoustic column is open at the fork and insert ends. The final
inequalities state the overlap geometry `40 cm ≤ L ≤ 80 cm` without fixing a
resonant value or frequency.
-/
structure MatchesSuppliedTelescopingTubeFigure
    (setup : TelescopingTubeResonanceSetup) : Prop where
  fixedTubeLengthCentimeters :
    lengthInCentimeters (setup.tubePartLength .fixedOuterTube) = 40
  insertLengthCentimeters :
    lengthInCentimeters (setup.tubePartLength .movableInsert) = 40
  fixedTubeArrow : ∀ observation,
    setup.figureMarkedLength observation
        .fixedTubeFortyCentimeters =
      setup.tubePartLength .fixedOuterTube
  insertArrow : ∀ observation,
    setup.figureMarkedLength observation
        .insertFortyCentimeters =
      setup.tubePartLength .movableInsert
  totalLengthArrowL : ∀ observation,
    setup.figureMarkedLength observation .totalLengthL =
      setup.tubeTotalLengthL observation
  insertTelescopes :
    setup.insertMobility = .telescopesAlongTubeAxis
  leftEndOpen :
    setup.boundaryCondition .leftByTuningFork = .openEnd
  rightEndOpen :
    setup.boundaryCondition .rightAtInsert = .openEnd
  forkBesideLeftOpening :
    setup.tuningForkPlacement = .nextToLeftOpenEnd
  tubeContainsAir : setup.medium = .airInsideTube
  overlapGeometry : ∀ observation (unit : LengthUnit),
    lengthReadout unit (setup.tubePartLength .fixedOuterTube) ≤
        lengthReadout unit (setup.tubeTotalLengthL observation) ∧
      lengthReadout unit (setup.tubeTotalLengthL observation) ≤
        lengthReadout unit (setup.tubePartLength .fixedOuterTube) +
          lengthReadout unit (setup.tubePartLength .movableInsert)

/-!
Numerical readouts stated in the prose: the three total lengths and sound
speed. Each listed configuration is an observed standing wave. There is no
frequency or wavelength value in this predicate.
-/
structure MatchesProblemAndResonanceReadouts
    (setup : TelescopingTubeResonanceSetup) : Prop where
  firstLengthCentimeters :
    lengthInCentimeters (setup.tubeTotalLengthL .first) = 425 / 10
  secondLengthCentimeters :
    lengthInCentimeters (setup.tubeTotalLengthL .second) = 567 / 10
  thirdLengthCentimeters :
    lengthInCentimeters (setup.tubeTotalLengthL .third) = 709 / 10
  soundSpeedMetersPerSecond :
    speedInMetersPerSecond setup.soundSpeed = 343
  standingWaveAtFirst : setup.standingWaveObserved .first
  standingWaveAtSecond : setup.standingWaveObserved .second
  standingWaveAtThird : setup.standingWaveObserved .third

/-!
The resonances were encountered successively while the insert was pulled out.
This is an observation-order input, not a numerical spacing or answer value.
-/
structure MatchesSuccessiveResonanceSequence
    (setup : TelescopingTubeResonanceSetup) : Prop where
  firstToSecond :
    setup.successivePulledOutResonance .first .second
  secondToThird :
    setup.successivePulledOutResonance .second .third

/-- Positivity and nondegeneracy conditions for the acoustic model. -/
structure HasPhysicalAcousticParameters
    (setup : TelescopingTubeResonanceSetup) : Prop where
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeed
  wavelengthPositive : 0 < lengthInMeters setup.soundWavelength
  tuningForkFrequencyPositive :
    0 < frequencyInHertz setup.tuningForkFrequency
  totalLengthsPositive : ∀ observation,
    0 < lengthInMeters (setup.tubeTotalLengthL observation)
  modeNumbersPositive : ∀ observation,
    0 < setup.longitudinalModeNumber observation

/-!
The open-open tube standing-wave law. At every observed resonance, twice the
effective acoustic length is an integral number of wavelengths. Successive
pulled-out resonances have consecutive longitudinal mode numbers. The law is
generic over observations and units and contains neither a derived wavelength
nor the requested tuning-fork frequency value.
-/
structure SatisfiesOpenTubeResonanceLaw
    (setup : TelescopingTubeResonanceSetup) : Prop where
  effectiveLengthModeRelation :
    ∀ (observation : ResonanceObservation) (unit : LengthUnit),
      setup.standingWaveObserved observation →
        2 *
            (lengthReadout unit (setup.tubeTotalLengthL observation) +
              lengthReadout unit setup.commonEndCorrection) =
          (setup.longitudinalModeNumber observation : ℝ) *
            lengthReadout unit setup.soundWavelength
  successiveModesAreConsecutive :
    ∀ earlier later,
      setup.successivePulledOutResonance earlier later →
        setup.longitudinalModeNumber later =
          setup.longitudinalModeNumber earlier + 1

/-!
The nondispersive acoustic-wave relation `v = λ f`, stated in every compatible
choice of length and time units. This governing law relates three independent
physical quantities and does not contain the requested numerical frequency.
-/
structure SatisfiesAcousticWaveSpeedLaw
    (setup : TelescopingTubeResonanceSetup) : Prop where
  speedEqualsWavelengthTimesFrequency :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.soundSpeed =
        lengthReadout lengthUnit setup.soundWavelength *
          frequencyReadout timeUnit setup.tuningForkFrequency

/-- Labels of the four answers printed with the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical kilohertz value printed beside each answer label. -/
def displayedAnswerFrequencyInKilohertz : AnswerChoice → ℝ
  | .A => 2415 / 1000
  | .B => 605 / 1000
  | .C => 807 / 1000
  | .D => 121 / 10

/-- Answer label recorded in the source dataset; this is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A setup's physical frequency is exactly the value printed for a choice. -/
def MatchesAnswerChoice
    (setup : TelescopingTubeResonanceSetup)
    (choice : AnswerChoice) : Prop :=
  frequencyInKilohertz setup.tuningForkFrequency =
    displayedAnswerFrequencyInKilohertz choice

/-- Conversion between the centimeter and meter readouts used here. -/
private lemma lengthInMeters_eq_lengthInCentimeters_div_hundred
    (length : LengthQuantity) :
    lengthInMeters length = lengthInCentimeters length / 100 := by
  let uCm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  change ((length UnitChoices.SI).val : ℝ) =
    ((length uCm).val : ℝ) / 100
  have hscale :
      UnitChoices.dimScale UnitChoices.SI uCm
          (dim (WithDim L𝓭 NNReal)) = (100 : NNReal) := by
    apply NNReal.eq
    dsimp [uCm]
    norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, LengthUnit.meters]
    rfl
  have h := congrArg (fun x : WithDim L𝓭 NNReal => (x.val : ℝ))
    (length.property UnitChoices.SI uCm)
  rw [hscale] at h
  norm_num [NNReal.smul_def] at h
  linarith

/-!
The separation of either pair of successive resonances is `14.2 cm`, so the
open-tube resonance law gives wavelength `2 * 14.2 cm = 0.284 m`.
-/
private lemma soundWavelengthInMeters_eq
    (setup : TelescopingTubeResonanceSetup)
    (hReadouts : MatchesProblemAndResonanceReadouts setup)
    (hSequence : MatchesSuccessiveResonanceSequence setup)
    (hResonance : SatisfiesOpenTubeResonanceLaw setup) :
    lengthInMeters setup.soundWavelength = (71 / 250 : ℝ) := by
  have hFirst := hResonance.effectiveLengthModeRelation
    .first LengthUnit.centimeters hReadouts.standingWaveAtFirst
  have hSecond := hResonance.effectiveLengthModeRelation
    .second LengthUnit.centimeters hReadouts.standingWaveAtSecond
  have hModes := hResonance.successiveModesAreConsecutive
    .first .second hSequence.firstToSecond
  change
    2 * (lengthInCentimeters (setup.tubeTotalLengthL .first) +
      lengthInCentimeters setup.commonEndCorrection) =
      (setup.longitudinalModeNumber .first : ℝ) *
        lengthInCentimeters setup.soundWavelength at hFirst
  change
    2 * (lengthInCentimeters (setup.tubeTotalLengthL .second) +
      lengthInCentimeters setup.commonEndCorrection) =
      (setup.longitudinalModeNumber .second : ℝ) *
        lengthInCentimeters setup.soundWavelength at hSecond
  rw [hReadouts.firstLengthCentimeters] at hFirst
  rw [hReadouts.secondLengthCentimeters, hModes] at hSecond
  norm_num [Nat.cast_add, Nat.cast_one] at hFirst hSecond
  have hWavelengthCentimeters :
      lengthInCentimeters setup.soundWavelength = (142 / 5 : ℝ) := by
    nlinarith [hFirst, hSecond]
  rw [lengthInMeters_eq_lengthInCentimeters_div_hundred,
    hWavelengthCentimeters]
  norm_num

/-!
Combining `λ = 0.284 m` with `v = λ f` and `v = 343 m/s` gives the
exact fork frequency `85750 / 71 Hz`.
-/
private lemma tuningForkFrequencyInHertz_eq
    (setup : TelescopingTubeResonanceSetup)
    (hReadouts : MatchesProblemAndResonanceReadouts setup)
    (hSequence : MatchesSuccessiveResonanceSequence setup)
    (hResonance : SatisfiesOpenTubeResonanceLaw setup)
    (hWave : SatisfiesAcousticWaveSpeedLaw setup) :
    frequencyInHertz setup.tuningForkFrequency =
      (85750 / 71 : ℝ) := by
  have hWavelength := soundWavelengthInMeters_eq
    setup hReadouts hSequence hResonance
  have hSpeedLaw := hWave.speedEqualsWavelengthTimesFrequency
    LengthUnit.meters TimeUnit.seconds
  change
    speedInMetersPerSecond setup.soundSpeed =
      lengthInMeters setup.soundWavelength *
        frequencyInHertz setup.tuningForkFrequency at hSpeedLaw
  rw [hReadouts.soundSpeedMetersPerSecond, hWavelength] at hSpeedLaw
  norm_num at hSpeedLaw ⊢
  linarith

/-!
The tuning fork has exact frequency `85750 / 71 Hz = 343 / 284 kHz`, about
`1.208 kHz`. None of the four printed source values equals that result; in
particular, recorded option `D = 12.1 kHz` differs by a factor of about ten.

This is the formal target corresponding to
`thm:physics:phyx_mini_0184:target`.
-/
theorem problem_phyx_mini_0184
    (setup : TelescopingTubeResonanceSetup)
    (hFigure : MatchesSuppliedTelescopingTubeFigure setup)
    (hReadouts : MatchesProblemAndResonanceReadouts setup)
    (hSequence : MatchesSuccessiveResonanceSequence setup)
    (hPhysical : HasPhysicalAcousticParameters setup)
    (hResonance : SatisfiesOpenTubeResonanceLaw setup)
    (hWave : SatisfiesAcousticWaveSpeedLaw setup) :
    frequencyInHertz setup.tuningForkFrequency =
        (85750 / 71 : ℝ) ∧
      frequencyInKilohertz setup.tuningForkFrequency =
        (343 / 284 : ℝ) ∧
      ∀ choice : AnswerChoice, ¬ MatchesAnswerChoice setup choice := by
  have hHz := tuningForkFrequencyInHertz_eq
    setup hReadouts hSequence hResonance hWave
  have hKHz :
      frequencyInKilohertz setup.tuningForkFrequency =
        (343 / 284 : ℝ) := by
    rw [frequencyInKilohertz, hHz]
    norm_num
  refine ⟨hHz, hKHz, ?_⟩
  intro choice
  cases choice <;>
    norm_num [MatchesAnswerChoice,
      displayedAnswerFrequencyInKilohertz, hKHz]

end PhyXMiniProblems.ProblemPhyXMini0184
