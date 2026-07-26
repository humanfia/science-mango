import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0190

open Dimension

/-!
# Wavelength of a sonar wave

The prose describes a ship using sonar in water and asks for the wavelength
of a `262 Hz` acoustic wave.  The primary bitmap labels the spacing between
successive wavefronts by `λ` and labels a propagation-velocity arrow by `v`.
It also uses an aircraft-like source icon and a ship receiver icon; these
diagram icons are recorded separately from the prose's sonar participants so
that the two pieces of supplied evidence are not silently conflated.

Frequency, wavelength, and propagation speed are unit-independent Physlib
quantities.  Real numbers occur only as readouts in explicitly selected units
and as the numerical values printed beside the answer choices.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A nonnegative acoustic frequency, with inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative wavelength, with length dimension. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative propagation speed, independent of the unit used to read it. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical frequency in inverse units of the selected time unit. -/
def frequencyReadout
    (unit : TimeUnit) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency {UnitChoices.SI with time := unit}).val : ℝ)

/-- Hertz readout, i.e. cycles per SI second. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout TimeUnit.seconds frequency

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Meter readout of a wavelength. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a speed in the selected length unit per selected time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Meter-per-second readout of the acoustic propagation speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-! ## Physical roles and primary-figure labels -/

/-- The physical locating system described in the prose. -/
inductive LocatingSystemKind where
  | shipSonar
  deriving DecidableEq, Repr

/-- Propagation medium relevant to the requested acoustic wavelength. -/
inductive AcousticMedium where
  | water
  deriving DecidableEq, Repr

/-- Qualitative wave type used by the locating system. -/
inductive AcousticWaveKind where
  | longitudinalTravelingSonarWave
  deriving DecidableEq, Repr

/-- Source and target roles in the prose's sonar scenario. -/
inductive SonarEndpointRole where
  | shipTransducer
  | underwaterObject
  deriving DecidableEq, Repr

/-- Object silhouettes actually visible in the supplied bitmap. -/
inductive FigureObjectIcon where
  | ship
  | aircraftLikeSource
  deriving DecidableEq, Repr

/-- Mathematical symbols printed in the bitmap. -/
inductive FigureQuantityLabel where
  | lambda
  | v
  deriving DecidableEq, Repr

/-- Direction of the wave pattern and green arrow in the bitmap. -/
inductive FigurePropagationDirection where
  | sourceIconTowardShip
  deriving DecidableEq, Repr

/--
The figure-derived objects and labeled quantities.  `wavefrontSpacing` and
`velocityArrowMagnitude` are physical quantities, not scalar placeholders.
-/
structure SonarWaveFigure where
  sourceIcon : FigureObjectIcon
  receiverIcon : FigureObjectIcon
  wavelengthLabel : FigureQuantityLabel
  velocityLabel : FigureQuantityLabel
  wavefrontSpacing : LengthQuantity
  velocityArrowMagnitude : SpeedQuantity
  propagationDirection : FigurePropagationDirection

/--
The physical wave together with the prose roles and associated diagram.
The wavelength is an independent unknown field and is not defined to be an
answer-choice value.
-/
structure SonarWaveSetup where
  locatingSystem : LocatingSystemKind
  medium : AcousticMedium
  waveKind : AcousticWaveKind
  sourceRole : SonarEndpointRole
  targetRole : SonarEndpointRole
  frequency : FrequencyQuantity
  wavelength : LengthQuantity
  propagationSpeed : SpeedQuantity
  figure : SonarWaveFigure

/-! ## Supplied data and physical laws -/

/--
Facts stated in the prose.  This predicate contains the given `262 Hz`
frequency but no numerical wavelength or answer label.
-/
structure MatchesProblemStatement (setup : SonarWaveSetup) : Prop where
  systemIsShipSonar : setup.locatingSystem = .shipSonar
  mediumIsWater : setup.medium = .water
  waveIsLongitudinalTravelingSound :
    setup.waveKind = .longitudinalTravelingSonarWave
  sourceIsShipTransducer : setup.sourceRole = .shipTransducer
  targetIsUnderwaterObject : setup.targetRole = .underwaterObject
  statedFrequencyHertz : frequencyInHertz setup.frequency = 262

/--
Readout of the primary bitmap: an aircraft-like source icon faces a ship,
the wavefront spacing is marked `λ`, and a green velocity arrow is marked
`v`.  The equalities identify the two pictured quantities with the modeled
wave quantities but assign neither one a requested numerical answer.
-/
structure MatchesSuppliedFigure (setup : SonarWaveSetup) : Prop where
  sourceIcon : setup.figure.sourceIcon = .aircraftLikeSource
  receiverIcon : setup.figure.receiverIcon = .ship
  wavelengthMarkedLambda : setup.figure.wavelengthLabel = .lambda
  velocityMarkedV : setup.figure.velocityLabel = .v
  spacingIsWavelength : setup.figure.wavefrontSpacing = setup.wavelength
  arrowMagnitudeIsPropagationSpeed :
    setup.figure.velocityArrowMagnitude = setup.propagationSpeed
  arrowDirection :
    setup.figure.propagationDirection = .sourceIconTowardShip

/-- Positivity conditions selecting an ordinary propagating acoustic wave. -/
structure HasPhysicalSonarWaveParameters (setup : SonarWaveSetup) : Prop where
  frequencyPositive : 0 < frequencyInHertz setup.frequency
  wavelengthPositive : 0 < lengthInMeters setup.wavelength
  propagationSpeedPositive :
    0 < speedInMetersPerSecond setup.propagationSpeed

/--
The standard textbook calibration used for the speed of sonar in water.
The source does not print a speed, so this auxiliary environmental datum is
kept separate from both the problem/figure observations and the wave law.
-/
def UsesStandardWaterSoundSpeed (setup : SonarWaveSetup) : Prop :=
  speedInMetersPerSecond setup.propagationSpeed = 1480

/--
Wave kinematics `v = f λ`, expressed in every compatible choice of length
and time units.  It contains no problem-specific wavelength or answer value.
-/
structure SatisfiesAcousticWaveKinematics (setup : SonarWaveSetup) : Prop where
  speedEqualsFrequencyTimesWavelength :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.propagationSpeed =
        frequencyReadout timeUnit setup.frequency *
          lengthReadout lengthUnit setup.wavelength

/-!
At `262 Hz` and `1480 m/s`, the wave law gives the exact modeled wavelength
`1480 / 262 = 740 / 131` meters.  This is derived rather than included in any
setup, figure, calibration, or law premise.
-/
lemma sonarWavelengthInMeters_eq_sevenHundredForty_div_oneHundredThirtyOne
    (setup : SonarWaveSetup)
    (h_problem : MatchesProblemStatement setup)
    (h_water_speed : UsesStandardWaterSoundSpeed setup)
    (h_law : SatisfiesAcousticWaveKinematics setup) :
    lengthInMeters setup.wavelength = 740 / 131 := by
  have h_wave :=
    h_law.speedEqualsFrequencyTimesWavelength
      LengthUnit.meters TimeUnit.seconds
  change
    speedInMetersPerSecond setup.propagationSpeed =
      frequencyInHertz setup.frequency * lengthInMeters setup.wavelength
    at h_wave
  rw [h_water_speed, h_problem.statedFrequencyHertz] at h_wave
  norm_num at h_wave ⊢
  linarith

/-! ## Displayed answers and formalization target -/

/-- Labels of the four wavelength choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Wavelength printed beside an answer label, measured in meters. -/
def displayedAnswerWavelengthMeters : AnswerChoice → ℝ
  | .A => 5.64
  | .B => 6.45
  | .C => 5.46
  | .D => 6.54

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/--
A displayed option is a closest listed approximation to the modeled physical
wavelength.  This compares all four supplied values and does not define the
unknown wavelength to equal any option.
-/
def IsClosestDisplayedWavelengthChoice
    (wavelength : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |lengthInMeters wavelength - displayedAnswerWavelengthMeters choice| ≤
      |lengthInMeters wavelength - displayedAnswerWavelengthMeters alternative|

/--
The sonar wavelength is `740/131 m` (approximately `5.65 m` under the standard
`1480 m/s` calibration), and the closest value among the supplied choices is
recorded answer A, printed as `5.64 m`.

This formalizes blueprint label `thm:physics:phyx_mini_0190:target`.
-/
theorem problem_phyx_mini_0190
    (setup : SonarWaveSetup)
    (h_problem : MatchesProblemStatement setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_physical : HasPhysicalSonarWaveParameters setup)
    (h_water_speed : UsesStandardWaterSoundSpeed setup)
    (h_law : SatisfiesAcousticWaveKinematics setup) :
    lengthInMeters setup.wavelength = 740 / 131 ∧
      IsClosestDisplayedWavelengthChoice
        setup.wavelength recordedDatasetAnswer := by
  have h_wavelength :=
    sonarWavelengthInMeters_eq_sevenHundredForty_div_oneHundredThirtyOne
      setup h_problem h_water_speed h_law
  constructor
  · exact h_wavelength
  · intro alternative
    rw [h_wavelength]
    cases alternative <;>
      norm_num [IsClosestDisplayedWavelengthChoice, recordedDatasetAnswer,
        displayedAnswerWavelengthMeters, abs_of_nonneg, abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0190
