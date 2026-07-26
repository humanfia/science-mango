import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Echolocation round-trip detection time

An animal emits a longitudinal sound pulse in water.  The pulse travels to an
obstacle, reflects, and returns to the animal.  The primary image identifies
the animal as a beluga whale in water; the problem text supplies the pulse
frequency and the one-way distance to the obstacle.

Lengths, durations, frequencies, and speeds are represented by Physlib
dimensionful quantities.  Real numbers occur only as explicitly named SI
readouts and as the displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0201

open Dimension

/-! ## Dimensionful acoustic quantities and SI readouts -/

/-- A nonnegative physical acoustic-path length. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical propagation duration. -/
abbrev AcousticDuration : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical acoustic frequency, carrying inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- Read a physical acoustic-path length as a real number of metres. -/
def lengthInMeters (length : AcousticLength) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical propagation duration as a real number of seconds. -/
def durationInSeconds (duration : AcousticDuration) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Read a physical acoustic frequency as a real number of hertz. -/
def frequencyInHertz (frequency : AcousticFrequency) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read Physlib's nonnegative dimensionful speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Physical setup and image/text labels -/

/-- The animal species identified by the primary image. -/
inductive EcholocatingAnimal where
  | belugaWhale
  deriving DecidableEq, Repr

/-- The propagation medium visible in the primary image. -/
inductive AcousticMedium where
  | water
  deriving DecidableEq, Repr

/-- Sound is modeled as the longitudinal wave stated in the problem. -/
inductive AcousticWaveMode where
  | longitudinal
  deriving DecidableEq, Repr

/-- The two legs of the pulse path before detection of the echo. -/
inductive EchoPathLeg where
  | outboundToObstacle
  | reflectedReturn
  deriving DecidableEq, Repr

/--
The physical quantities and labels of the echolocation experiment.

`reflectionDetectionDelay` is an unknown physical duration.  In particular,
this structure does not assign it any displayed answer value.
-/
structure EcholocationSetup where
  animal : EcholocatingAnimal
  medium : AcousticMedium
  waveMode : AcousticWaveMode
  emittedFrequency : AcousticFrequency
  oneWayObstacleDistance : AcousticLength
  soundSpeed : DimSpeed
  pathLength : EchoPathLeg → AcousticLength
  pathTravelTime : EchoPathLeg → AcousticDuration
  reflectionDetectionDelay : AcousticDuration

/--
Problem-text and primary-image data: a beluga in water emits a longitudinal
`100000 Hz` pulse toward an obstacle `100 m` away.  Reflection makes both path
legs have the stated one-way length.  No detection-time answer occurs here.
-/
structure MatchesProblemAndFigure (setup : EcholocationSetup) : Prop where
  animalIsBeluga : setup.animal = .belugaWhale
  mediumIsWater : setup.medium = .water
  pulseIsLongitudinal : setup.waveMode = .longitudinal
  emittedFrequencyReadout : frequencyInHertz setup.emittedFrequency = 100000
  obstacleDistanceReadout :
    lengthInMeters setup.oneWayObstacleDistance = 100
  outboundLengthReadout :
    lengthInMeters (setup.pathLength .outboundToObstacle) =
      lengthInMeters setup.oneWayObstacleDistance
  reflectedReturnLengthReadout :
    lengthInMeters (setup.pathLength .reflectedReturn) =
      lengthInMeters setup.oneWayObstacleDistance

/--
The textbook water-sound-speed calibration implicit in the supplied answer
table.  This is auxiliary physical data, not the requested detection delay.
-/
structure UsesTextbookWaterSoundSpeed (setup : EcholocationSetup) : Prop where
  soundSpeedReadout : speedInMetersPerSecond setup.soundSpeed = 1400

/-- Strict positivity conditions for the emitted wave and propagation data. -/
structure HasPhysicalEcholocationParameters
    (setup : EcholocationSetup) : Prop where
  frequencyPositive : 0 < frequencyInHertz setup.emittedFrequency
  obstacleDistancePositive :
    0 < lengthInMeters setup.oneWayObstacleDistance
  soundSpeedPositive : 0 < speedInMetersPerSecond setup.soundSpeed
  legLengthsPositive :
    ∀ leg, 0 < lengthInMeters (setup.pathLength leg)

/--
Governing laws for the echo.  Constant-speed travel holds on the outbound and
reflected-return legs, and the detection delay is the sum of their travel
times.  These laws contain no numerical value for the requested delay.
-/
structure SatisfiesRoundTripSoundPropagation
    (setup : EcholocationSetup) : Prop where
  constantSpeedTravel : ∀ leg,
    durationInSeconds (setup.pathTravelTime leg) *
        speedInMetersPerSecond setup.soundSpeed =
      lengthInMeters (setup.pathLength leg)
  detectionAfterReturn :
    durationInSeconds setup.reflectionDetectionDelay =
      durationInSeconds (setup.pathTravelTime .outboundToObstacle) +
        durationInSeconds (setup.pathTravelTime .reflectedReturn)

/-! ## Displayed answers and formalization target -/

/-- Labels of the four answers displayed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Seconds printed beside each displayed answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 1 / 5
  | .B => 9 / 50
  | .C => 4 / 25
  | .D => 7 / 50

/--
A physical duration agrees with a displayed hundredth-second answer.  The
half-centisecond tolerance models rounding to the printed precision.
-/
def MatchesAnswerChoice
    (duration : AcousticDuration) (choice : AnswerChoice) : Prop :=
  |durationInSeconds duration - choice.seconds| ≤ 1 / 200

/-- A displayed choice is uniquely closest to the physical duration. -/
def IsClosestAnswerChoice
    (duration : AcousticDuration) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |durationInSeconds duration - choice.seconds| <
      |durationInSeconds duration - other.seconds|

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
Before rounding to the precision of the choices, the ideal round-trip model
gives an exact detection delay of `1/7 s`.
-/
lemma reflectionDetectionDelay_exact
    (setup : EcholocationSetup)
    (h_problem : MatchesProblemAndFigure setup)
    (h_speed : UsesTextbookWaterSoundSpeed setup)
    (h_physical : HasPhysicalEcholocationParameters setup)
    (h_propagation : SatisfiesRoundTripSoundPropagation setup) :
    durationInSeconds setup.reflectionDetectionDelay = (1 : ℝ) / 7 := by
  have h_out :=
    h_propagation.constantSpeedTravel EchoPathLeg.outboundToObstacle
  rw [h_speed.soundSpeedReadout, h_problem.outboundLengthReadout,
    h_problem.obstacleDistanceReadout] at h_out
  have h_return :=
    h_propagation.constantSpeedTravel EchoPathLeg.reflectedReturn
  rw [h_speed.soundSpeedReadout, h_problem.reflectedReturnLengthReadout,
    h_problem.obstacleDistanceReadout] at h_return
  rw [h_propagation.detectionAfterReturn]
  linarith

/--
Physics formalization target `thm:physics:phyx_mini_0201:target`: the reflected
pulse is detected after approximately `0.14 s`, and recorded choice D is the
unique closest displayed answer.
-/
theorem reflectionDetectionDelay_matches_recordedAnswerD
    (setup : EcholocationSetup)
    (h_problem : MatchesProblemAndFigure setup)
    (h_speed : UsesTextbookWaterSoundSpeed setup)
    (h_physical : HasPhysicalEcholocationParameters setup)
    (h_propagation : SatisfiesRoundTripSoundPropagation setup) :
    MatchesAnswerChoice setup.reflectionDetectionDelay recordedAnswerChoice ∧
      IsClosestAnswerChoice setup.reflectionDetectionDelay
        recordedAnswerChoice := by
  have h_exact :=
    reflectionDetectionDelay_exact setup h_problem h_speed h_physical h_propagation
  constructor
  · norm_num [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.seconds,
      h_exact, abs_of_nonneg]
  · intro other h_other
    rw [h_exact]
    cases other with
    | A => norm_num [recordedAnswerChoice, AnswerChoice.seconds]
    | B => norm_num [recordedAnswerChoice, AnswerChoice.seconds]
    | C => norm_num [recordedAnswerChoice, AnswerChoice.seconds]
    | D => simp [recordedAnswerChoice] at h_other

end PhyXMiniProblems.ProblemPhyXMini0201
