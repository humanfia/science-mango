import Mathlib.Algebra.Order.Round
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Simultaneous reception of a boat horn in air and water

A boat horn is heard simultaneously by a friend on land and by a submerged
diver directly below the horn.  The sound path to the friend lies entirely in
air.  The vertical path to the diver consists of an air leg from the horn to
the lake surface followed by a water leg.

Lengths, durations, and sound speeds are represented by Physlib dimensionful
quantities.  Real numbers are used only for explicitly named SI readouts and
for the Celsius temperature readouts supplied by the problem.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0168

open Dimension

/-! ## Dimensionful acoustic quantities -/

/-- A physical acoustic-path length, independent of the chosen unit readout. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical propagation duration, independent of the chosen unit readout. -/
abbrev AcousticDuration : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical sound speed, carrying the length-per-time dimension. -/
abbrev AcousticSpeed : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length as a real number of metres. -/
def metersValue (length : AcousticLength) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical duration as a real number of seconds. -/
def secondsValue (duration : AcousticDuration) : ℝ :=
  (duration UnitChoices.SI).val

/-- Read a physical speed as a real number of metres per second. -/
def metersPerSecondValue (speed : AcousticSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/-! ## Physical setup and figure labels -/

/-- The two media traversed by the sound in the problem. -/
inductive SoundMedium where
  | air
  | water
  deriving DecidableEq, Repr

/--
The three constant-medium path legs used to compare the two listeners' travel
times.  The latter two legs concatenate to form the vertical horn-to-diver
path marked `?` in the figure.
-/
inductive SoundPathLeg where
  | hornToFriend
  | hornToSurface
  | surfaceToDiver
  deriving DecidableEq, Repr

/--
Physical quantities for the boat-horn experiment.

The temperature function stores Celsius readouts, while lengths, times, and
speeds themselves remain dimensionful quantities.  In particular, no
numerical value for the requested `hornToDiverDistance` is stored here.
-/
structure BoatHornDiverSetup where
  /-- Medium traversed by each named path leg. -/
  pathMedium : SoundPathLeg → SoundMedium
  /-- Physical length of each constant-medium path leg. -/
  pathLength : SoundPathLeg → AcousticLength
  /-- Propagation duration along each constant-medium path leg. -/
  travelTime : SoundPathLeg → AcousticDuration
  /-- Sound speed in each medium at the stated temperature. -/
  soundSpeed : SoundMedium → AcousticSpeed
  /-- Temperature of each medium, read in degrees Celsius. -/
  temperatureCelsius : SoundMedium → ℝ
  /-- Full vertical distance from the horn to the diver, labeled `?`. -/
  hornToDiverDistance : AcousticLength

/--
Problem-text and primary-figure information.

The direct horn-to-friend sound path is labeled `22.0 m`; the horn is `1.2 m`
above the lake surface; and the diver is directly below the horn, so the
requested vertical distance is the sum of its air and water legs.  This does
not state the requested numerical distance.
-/
structure MatchesProblemAndFigure (setup : BoatHornDiverSetup) : Prop where
  friendPathIsInAir :
    setup.pathMedium .hornToFriend = .air
  hornToSurfacePathIsInAir :
    setup.pathMedium .hornToSurface = .air
  surfaceToDiverPathIsInWater :
    setup.pathMedium .surfaceToDiver = .water
  hornToFriendReadout :
    metersValue (setup.pathLength .hornToFriend) = 22
  hornHeightAboveSurfaceReadout :
    metersValue (setup.pathLength .hornToSurface) = (6 : ℝ) / 5
  verticalPathSegmentSum :
    metersValue setup.hornToDiverDistance =
      metersValue (setup.pathLength .hornToSurface) +
        metersValue (setup.pathLength .surfaceToDiver)

/--
Temperature and standard sound-speed readouts used for air and fresh water at
`20 °C`: `344 m/s` in air and `1482 m/s` in water.  These are calibration
data, not the requested distance.
-/
structure MatchesSoundSpeedDataAt20C (setup : BoatHornDiverSetup) : Prop where
  airTemperatureReadout :
    setup.temperatureCelsius .air = 20
  waterTemperatureReadout :
    setup.temperatureCelsius .water = 20
  airSoundSpeedReadout :
    metersPerSecondValue (setup.soundSpeed .air) = 344
  waterSoundSpeedReadout :
    metersPerSecondValue (setup.soundSpeed .water) = 1482

/-- Positivity and nonnegativity conditions for the physical setup. -/
structure HasPhysicalParameters (setup : BoatHornDiverSetup) : Prop where
  pathLengthsPositive :
    ∀ leg, 0 < metersValue (setup.pathLength leg)
  travelTimesNonnegative :
    ∀ leg, 0 ≤ secondsValue (setup.travelTime leg)
  soundSpeedsPositive :
    ∀ medium, 0 < metersPerSecondValue (setup.soundSpeed medium)
  hornToDiverDistancePositive :
    0 < metersValue setup.hornToDiverDistance

/--
Governing propagation and reception-time laws.

Constant-speed travel on each homogeneous leg gives `distance = speed × time`.
Because the same horn emission reaches both listeners simultaneously, the air
travel time to the friend equals the sum of the vertical air and water travel
times to the diver.  Neither law contains the numerical answer.
-/
structure SatisfiesSoundPropagationLaws (setup : BoatHornDiverSetup) : Prop where
  constantSpeedTravel : ∀ leg,
    secondsValue (setup.travelTime leg) *
        metersPerSecondValue (setup.soundSpeed (setup.pathMedium leg)) =
      metersValue (setup.pathLength leg)
  simultaneousReception :
    secondsValue (setup.travelTime .hornToFriend) =
      secondsValue (setup.travelTime .hornToSurface) +
        secondsValue (setup.travelTime .surfaceToDiver)

/-! ## Derived distance and displayed answers -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre readout printed beside each displayed answer choice. -/
def answerChoiceMeters : AnswerChoice → ℝ
  | .A => 908 / 10
  | .B => 948 / 10
  | .C => 858 / 10
  | .D => 658 / 10

/-- A displayed choice is uniquely closest to an actual metre readout. -/
def IsClosestAnswerChoice (actualMeters : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |actualMeters - answerChoiceMeters choice| <
      |actualMeters - answerChoiceMeters other|

/--
Before rounding to the precision of the choices, the idealized equal-arrival
model gives `19524 / 215 m` for the full horn-to-diver distance.
-/
lemma hornToDiverDistance_exact
    (setup : BoatHornDiverSetup)
    (hFigure : MatchesProblemAndFigure setup)
    (hSpeedData : MatchesSoundSpeedDataAt20C setup)
    (hPhysical : HasPhysicalParameters setup)
    (hPropagation : SatisfiesSoundPropagationLaws setup) :
    metersValue setup.hornToDiverDistance = (19524 : ℝ) / 215 := by
  have hFriend := hPropagation.constantSpeedTravel .hornToFriend
  have hSurface := hPropagation.constantSpeedTravel .hornToSurface
  have hWater := hPropagation.constantSpeedTravel .surfaceToDiver
  rw [hFigure.friendPathIsInAir, hSpeedData.airSoundSpeedReadout,
    hFigure.hornToFriendReadout] at hFriend
  rw [hFigure.hornToSurfacePathIsInAir, hSpeedData.airSoundSpeedReadout,
    hFigure.hornHeightAboveSurfaceReadout] at hSurface
  rw [hFigure.surfaceToDiverPathIsInWater, hSpeedData.waterSoundSpeedReadout] at hWater
  rw [hFigure.verticalPathSegmentSum, hFigure.hornHeightAboveSurfaceReadout]
  norm_num at hFriend hSurface ⊢
  nlinarith [hPropagation.simultaneousReception]

/--
Physics formalization target for
`thm:physics:phyx_mini_0168:target`: the requested distance rounds to
`90.8 m` at the precision of the answer table, and choice A is uniquely
closest to the idealized value.
-/
theorem hornToDiverDistance_rounds_to_answerA
    (setup : BoatHornDiverSetup)
    (hFigure : MatchesProblemAndFigure setup)
    (hSpeedData : MatchesSoundSpeedDataAt20C setup)
    (hPhysical : HasPhysicalParameters setup)
    (hPropagation : SatisfiesSoundPropagationLaws setup) :
    round (10 * metersValue setup.hornToDiverDistance) = 908 ∧
      IsClosestAnswerChoice (metersValue setup.hornToDiverDistance) .A := by
  rw [hornToDiverDistance_exact setup hFigure hSpeedData hPhysical hPropagation]
  constructor
  · norm_num
  · intro other hOther
    cases other with
    | A => exact (hOther rfl).elim
    | B => norm_num [answerChoiceMeters]
    | C => norm_num [answerChoiceMeters]
    | D => norm_num [answerChoiceMeters]

end PhyXMiniProblems.ProblemPhyXMini0168
