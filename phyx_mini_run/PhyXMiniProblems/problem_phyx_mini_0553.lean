import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0553

/-!
# A missile launched from a relativistic spaceship

The Earth origin `O` and spaceship origin `O'` determine two inertial frames.
The spaceship moves rightward at `0.80c` as measured from Earth, and the
missile moves rightward at `0.60c` as measured in the spaceship frame. The
requested quantity is the missile speed measured from Earth.

Speeds are represented by Physlib's unit-independent `DimSpeed`. Real numbers
occur only as readouts in named units, dimensionless fractions of the vacuum
speed of light, qualitative drawing coordinates, and displayed answer values.
-/

/-! ## Dimensionful speed and scalar readouts -/

/-- A nonnegative physical speed magnitude, independent of the unit system. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical speed in selected units of length and time. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read Physlib's exact dimensionful vacuum speed of light in named units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- A physical speed expressed as a dimensionless fraction of vacuum `c`. -/
def speedFractionOfVacuumLight (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-! ## Frames, origins, directions, and primary-figure labels -/

/-- The two inertial frames used for the three speed measurements. -/
inductive InertialFrameLabel where
  | earthRestFrame
  | spaceshipRestFrame
  deriving DecidableEq, Repr

/-- The two reference origins printed in the primary image. -/
inductive FrameOriginLabel where
  | O
  | OPrime
  deriving DecidableEq, Repr

/-- The frame represented by each labeled origin. -/
def originFrame : FrameOriginLabel → InertialFrameLabel
  | .O => .earthRestFrame
  | .OPrime => .spaceshipRestFrame

/-- Direction along the horizontal axis of the drawing. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- The two blue speed arrows printed at the front of the spaceship. -/
inductive FigureVelocityArrow where
  | missileRelativeToSpaceship
  | spaceshipRelativeToEarth
  deriving DecidableEq, Repr

/-!
Typed evidence carried by the primary image. Origin coordinates express only
left-to-right visual ordering and are not physical distances.
-/
structure EarthSpaceshipMissileFigure where
  showsEarth : Bool
  showsSpaceship : Bool
  originHorizontalCoordinate : FrameOriginLabel → ℝ
  originText : FrameOriginLabel → String
  arrowDirection : FigureVelocityArrow → HorizontalDirection
  arrowText : FigureVelocityArrow → String
  upperArrow : FigureVelocityArrow
  lowerArrow : FigureVelocityArrow
  hasQuantitativePositionScale : Bool

/-!
All frame assignments and physical speed magnitudes in the scenario. The
requested `missileSpeedMeasuredByEarth` is an independent field: it is not
defined using an answer choice or a solved numerical expression.
-/
structure EarthSpaceshipMissileSetup where
  spaceshipSpeedObserverFrame : InertialFrameLabel
  missileLaunchSpeedObserverFrame : InertialFrameLabel
  requestedSpeedObserverFrame : InertialFrameLabel
  spaceshipMotionInEarthFrame : HorizontalDirection
  missileMotionInSpaceshipFrame : HorizontalDirection
  missileMotionInEarthFrame : HorizontalDirection
  spaceshipSpeedMeasuredByEarth : SpeedQuantity
  missileSpeedMeasuredBySpaceship : SpeedQuantity
  missileSpeedMeasuredByEarth : SpeedQuantity
  figure : EarthSpaceshipMissileFigure

/-! ## Figure evidence and stated numerical data -/

/-!
Facts read directly from the bitmap: `O` lies on Earth to the left of `O'` on
the spaceship; both arrows point right; the upper arrow is labeled
`v' = 0.60c`; and the lower arrow is labeled `u = 0.80c`.
-/
structure MatchesPrimaryFigure
    (setup : EarthSpaceshipMissileSetup) : Prop where
  earthIsShown : setup.figure.showsEarth = true
  spaceshipIsShown : setup.figure.showsSpaceship = true
  earthOriginLeftOfSpaceshipOrigin :
    setup.figure.originHorizontalCoordinate .O <
      setup.figure.originHorizontalCoordinate .OPrime
  earthOriginText : setup.figure.originText .O = "O"
  spaceshipOriginText : setup.figure.originText .OPrime = "O'"
  missileArrowPointsRight :
    setup.figure.arrowDirection .missileRelativeToSpaceship = .rightward
  spaceshipArrowPointsRight :
    setup.figure.arrowDirection .spaceshipRelativeToEarth = .rightward
  missileArrowIsUpper :
    setup.figure.upperArrow = .missileRelativeToSpaceship
  spaceshipArrowIsLower :
    setup.figure.lowerArrow = .spaceshipRelativeToEarth
  missileArrowText :
    setup.figure.arrowText .missileRelativeToSpaceship = "v' = 0.60c"
  spaceshipArrowText :
    setup.figure.arrowText .spaceshipRelativeToEarth = "u = 0.80c"
  noQuantitativePositionScale :
    setup.figure.hasQuantitativePositionScale = false

/-!
Frame assignments, same-direction motion, and the two numerical speed readouts
supplied by the problem. No Earth-frame missile speed is supplied.
-/
structure MatchesProblemData
    (setup : EarthSpaceshipMissileSetup) : Prop where
  spaceshipSpeedMeasuredInEarthFrame :
    setup.spaceshipSpeedObserverFrame = .earthRestFrame
  missileLaunchSpeedMeasuredInSpaceshipFrame :
    setup.missileLaunchSpeedObserverFrame = .spaceshipRestFrame
  requestedSpeedMeasuredInEarthFrame :
    setup.requestedSpeedObserverFrame = .earthRestFrame
  spaceshipMovesRightFromEarth :
    setup.spaceshipMotionInEarthFrame = .rightward
  missileMovesRightFromSpaceship :
    setup.missileMotionInSpaceshipFrame = .rightward
  missileMovesRightFromEarth :
    setup.missileMotionInEarthFrame = .rightward
  spaceshipSpeedFraction :
    speedFractionOfVacuumLight setup.spaceshipSpeedMeasuredByEarth = 4 / 5
  missileLaunchSpeedFraction :
    speedFractionOfVacuumLight setup.missileSpeedMeasuredBySpaceship = 3 / 5
  matchesFigure : MatchesPrimaryFigure setup

/-!
Physical domain conditions for the three speed magnitudes. These state only
positivity and subluminality; in particular, they do not determine the unknown
Earth-frame missile speed.
-/
structure HasPhysicalSpeedParameters
    (setup : EarthSpaceshipMissileSetup) : Prop where
  lightSpeedReadoutPositive :
    0 < vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds
  spaceshipSpeedPositive :
    0 < speedFractionOfVacuumLight setup.spaceshipSpeedMeasuredByEarth
  spaceshipSpeedSubluminal :
    speedFractionOfVacuumLight setup.spaceshipSpeedMeasuredByEarth < 1
  missileLaunchSpeedPositive :
    0 < speedFractionOfVacuumLight setup.missileSpeedMeasuredBySpaceship
  missileLaunchSpeedSubluminal :
    speedFractionOfVacuumLight setup.missileSpeedMeasuredBySpaceship < 1
  missileEarthSpeedPositive :
    0 < speedFractionOfVacuumLight setup.missileSpeedMeasuredByEarth
  missileEarthSpeedSubluminal :
    speedFractionOfVacuumLight setup.missileSpeedMeasuredByEarth < 1

/-! ## Governing special-relativistic law -/

/-!
Collinear Einstein velocity addition for motion in the same direction, written
in dimensionless fractions of `c`:

`w/c = ((u/c) + (v'/c)) / (1 + (u/c)(v'/c))`.

This governing relation contains neither an answer-choice label nor the solved
fraction `35/37`.
-/
structure SatisfiesCollinearEinsteinVelocityAddition
    (setup : EarthSpaceshipMissileSetup) : Prop where
  missileVelocityTransformation :
    speedFractionOfVacuumLight setup.missileSpeedMeasuredByEarth =
      (speedFractionOfVacuumLight setup.spaceshipSpeedMeasuredByEarth +
          speedFractionOfVacuumLight
            setup.missileSpeedMeasuredBySpaceship) /
        (1 +
          speedFractionOfVacuumLight setup.spaceshipSpeedMeasuredByEarth *
            speedFractionOfVacuumLight
              setup.missileSpeedMeasuredBySpaceship)

/-! ## Displayed answers and current target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The speed coefficient multiplying `c` beside each displayed choice. -/
def displayedSpeedFraction : AnswerChoice → ℝ
  | .A => 3 / 5
  | .B => 4 / 5
  | .C => 1 / 4
  | .D => 19 / 20

/-- The answer label recorded by the source dataset; it is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a speed fraction displayed to the nearest hundredth. -/
def RoundsToNearestHundredth
    (actualFraction displayedFraction : ℝ) : Prop :=
  |actualFraction - displayedFraction| < 1 / 200

/-- A displayed choice agrees with the modeled Earth-frame missile speed. -/
def MatchesAnswerChoice
    (setup : EarthSpaceshipMissileSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredth
    (speedFractionOfVacuumLight setup.missileSpeedMeasuredByEarth)
    (displayedSpeedFraction choice)

/-- The selected choice is the unique displayed rounded value. -/
def IsUniqueMatchingAnswerChoice
    (setup : EarthSpaceshipMissileSetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice, MatchesAnswerChoice setup other → other = choice

/-!
Substitution of `u/c = 4/5` and `v'/c = 3/5` into the governing law gives the
exact Earth-frame missile speed fraction

`(4/5 + 3/5) / (1 + (4/5)(3/5)) = 35/37`.

This is a derived result and does not occur in a data or law premise.
-/
lemma missile_speed_fraction_measured_by_earth
    (setup : EarthSpaceshipMissileSetup)
    (hData : MatchesProblemData setup)
    (hRelativity : SatisfiesCollinearEinsteinVelocityAddition setup) :
    speedFractionOfVacuumLight setup.missileSpeedMeasuredByEarth =
      35 / 37 := by
  rw [hRelativity.missileVelocityTransformation,
    hData.spaceshipSpeedFraction, hData.missileLaunchSpeedFraction]
  norm_num

/-!
The exact fraction `35/37 ≈ 0.945946` rounds to `0.95`, uniquely selecting
choice D. The rounded displayed value is deliberately not asserted as an exact
physical equality.

This formalizes `thm:physics:phyx_mini_0553:target`.
-/
theorem problem_phyx_mini_0553
    (setup : EarthSpaceshipMissileSetup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalSpeedParameters setup)
    (hRelativity : SatisfiesCollinearEinsteinVelocityAddition setup) :
    speedFractionOfVacuumLight setup.missileSpeedMeasuredByEarth =
        35 / 37 ∧
      IsUniqueMatchingAnswerChoice setup recordedDatasetAnswer := by
  have hSpeed :
      speedFractionOfVacuumLight setup.missileSpeedMeasuredByEarth =
        35 / 37 :=
    missile_speed_fraction_measured_by_earth setup hData hRelativity
  refine ⟨hSpeed, ?_⟩
  constructor
  · norm_num [MatchesAnswerChoice, RoundsToNearestHundredth,
      recordedDatasetAnswer, displayedSpeedFraction, hSpeed, abs_of_nonpos]
  · intro other hOther
    cases other with
    | A =>
        norm_num [MatchesAnswerChoice, RoundsToNearestHundredth,
          displayedSpeedFraction, hSpeed, abs_of_nonneg] at hOther
    | B =>
        norm_num [MatchesAnswerChoice, RoundsToNearestHundredth,
          displayedSpeedFraction, hSpeed, abs_of_nonneg] at hOther
    | C =>
        norm_num [MatchesAnswerChoice, RoundsToNearestHundredth,
          displayedSpeedFraction, hSpeed, abs_of_nonneg] at hOther
    | D => rfl

end ProblemPhyXMini0553

end PhyXMiniProblems
