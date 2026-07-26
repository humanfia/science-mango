import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Relativistic missile interception

An enemy spacecraft approaches a starfighter at `0.400 c` in the
starfighter's rest frame.  It launches a missile toward the starfighter at
`0.700 c` in the enemy's rest frame.  At launch the two spacecraft are
`8.00 * 10^6 km` apart in the starfighter frame.

Lengths, elapsed times, and signed axial velocities are represented by
Physlib dimensionful quantities.  Real numbers below are only readouts in
named units, dimensionless fractions of the speed of light, figure ranks, or
displayed answer values.  Positive velocity points from the enemy toward the
starfighter, matching the left-to-right orientation of the supplied figure.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0512

open Dimension

/-! ## Dimensionful quantities and calibrated readouts -/

/-- A nonnegative physical separation. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative elapsed physical time. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-!
A signed one-dimensional physical velocity.  Physlib's `DimSpeed` is
nonnegative, whereas this problem needs an axial sign to distinguish motion
toward the starfighter from motion toward the enemy.
-/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read an elapsed time in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed axial velocity in compatible length and time units. -/
def axialVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : AxialVelocity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read Physlib's exact vacuum speed of light in compatible units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Kilometer readout of the launch separation. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Second readout of the requested flight time. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-! ## Reference frames, bodies, directions, and primary-figure labels -/

/-- The two inertial rest frames named by the problem. -/
inductive InertialFrame where
  | enemyRest
  | starfighterRest
  deriving DecidableEq, Repr

/-- The three physical bodies shown from left to right in the figure. -/
inductive BodyLabel where
  | enemyShip
  | missile
  | starfighter
  deriving DecidableEq, Repr

/-!
Directions along the common line of motion.  `towardStarfighter` is the
positive axial direction used by `axialVelocityReadout`.
-/
inductive AxialDirection where
  | towardEnemy
  | towardStarfighter
  deriving DecidableEq, Repr

/-- The two printed text labels in the supplied image. -/
inductive PrintedFigureLabel where
  | enemy
  | starfighter
  deriving DecidableEq, Repr

/-- The pale line and green arrow drawn between the three bodies. -/
inductive ConnectorStyle where
  | lightGreenLine
  | greenTrajectoryArrow
  deriving DecidableEq, Repr

/-!
Qualitative evidence extracted from the primary image.  The natural-number
rank is only a left-to-right drawing order, not a physical coordinate or
distance measurement.
-/
structure SpaceshipMissileFigure where
  shows : BodyLabel → Bool
  leftToRightRank : BodyLabel → ℕ
  hasPrintedLabel : BodyLabel → Bool
  printedLabelTarget : PrintedFigureLabel → BodyLabel
  connectorFrom : ConnectorStyle → BodyLabel
  connectorTo : ConnectorStyle → BodyLabel

/-!
Independent physical observables for the interception scenario.

The missile velocity in the starfighter frame and its flight time are stored
as unknown physical quantities.  Neither is defined from an answer choice or
from the desired numerical result.
-/
structure RelativisticMissileSetup where
  figure : SpaceshipMissileFigure
  launchVehicle : BodyLabel
  targetVehicle : BodyLabel
  requestedMeasurementFrame : InertialFrame
  separationFrom : BodyLabel
  separationTo : BodyLabel
  firingSeparation : LengthQuantity
  velocityInFrame : BodyLabel → InertialFrame → AxialVelocity
  motionDirectionInFrame : BodyLabel → InertialFrame → AxialDirection
  flightTimeInStarfighterFrame : DurationQuantity

/-! ## Problem data, primary-image readouts, and physical admissibility -/

/-- The named rest frames really are rest frames of their defining craft. -/
structure MatchesNamedRestFrames
    (setup : RelativisticMissileSetup) : Prop where
  enemyAtRestInEnemyFrame :
    ∀ lengthUnit timeUnit,
      axialVelocityReadout lengthUnit timeUnit
          (setup.velocityInFrame .enemyShip .enemyRest) = 0
  starfighterAtRestInStarfighterFrame :
    ∀ lengthUnit timeUnit,
      axialVelocityReadout lengthUnit timeUnit
          (setup.velocityInFrame .starfighter .starfighterRest) = 0

/-!
Numerical and qualitative data stated in the problem.  The two velocity
readouts are fractions of the same physical speed of light in every compatible
unit choice.  This predicate gives no starfighter-frame missile speed and no
flight-time answer.
-/
structure MatchesProblemStatement
    (setup : RelativisticMissileSetup) : Prop where
  launchedByEnemy : setup.launchVehicle = .enemyShip
  targetIsStarfighter : setup.targetVehicle = .starfighter
  asksForStarfighterFrame :
    setup.requestedMeasurementFrame = .starfighterRest
  separationStartsAtEnemy : setup.separationFrom = .enemyShip
  separationEndsAtStarfighter : setup.separationTo = .starfighter
  firingSeparationKilometers :
    lengthInKilometers setup.firingSeparation = 8 * 10 ^ 6
  enemyMovesTowardStarfighter :
    setup.motionDirectionInFrame .enemyShip .starfighterRest =
      .towardStarfighter
  missileMovesTowardStarfighterInEnemyFrame :
    setup.motionDirectionInFrame .missile .enemyRest = .towardStarfighter
  enemyVelocityIsPointFourC :
    ∀ lengthUnit timeUnit,
      axialVelocityReadout lengthUnit timeUnit
          (setup.velocityInFrame .enemyShip .starfighterRest) =
        (2 / 5 : ℝ) *
          vacuumSpeedOfLightReadout lengthUnit timeUnit
  missileVelocityRelativeToEnemyIsPointSevenC :
    ∀ lengthUnit timeUnit,
      axialVelocityReadout lengthUnit timeUnit
          (setup.velocityInFrame .missile .enemyRest) =
        (7 / 10 : ℝ) *
          vacuumSpeedOfLightReadout lengthUnit timeUnit

/-!
Figure facts visible in the supplied raster: enemy, missile, and starfighter
occur from left to right; only the two spacecraft carry printed labels; the
pale connector runs from enemy to missile; and the green trajectory arrow
points from missile to starfighter.  The image supplies no quantitative scale.
-/
structure MatchesSuppliedFigure
    (figure : SpaceshipMissileFigure) : Prop where
  everyBodyShown : ∀ body, figure.shows body = true
  enemyIsLeftmost : figure.leftToRightRank .enemyShip = 0
  missileIsInCenter : figure.leftToRightRank .missile = 1
  starfighterIsRightmost : figure.leftToRightRank .starfighter = 2
  enemyHasPrintedLabel : figure.hasPrintedLabel .enemyShip = true
  missileHasNoPrintedLabel : figure.hasPrintedLabel .missile = false
  starfighterHasPrintedLabel : figure.hasPrintedLabel .starfighter = true
  enemyLabelTarget : figure.printedLabelTarget .enemy = .enemyShip
  starfighterLabelTarget :
    figure.printedLabelTarget .starfighter = .starfighter
  paleLineStartsAtEnemy :
    figure.connectorFrom .lightGreenLine = .enemyShip
  paleLineEndsAtMissile : figure.connectorTo .lightGreenLine = .missile
  trajectoryStartsAtMissile :
    figure.connectorFrom .greenTrajectoryArrow = .missile
  trajectoryPointsToStarfighter :
    figure.connectorTo .greenTrajectoryArrow = .starfighter

/-!
Positivity and subluminality conditions for the one-dimensional model.  These
conditions exclude degenerate inputs without assigning the unknown missile
speed or flight time a requested numerical value.
-/
structure HasPhysicalRelativisticParameters
    (setup : RelativisticMissileSetup) : Prop where
  lightSpeedPositive :
    0 < vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds
  firingSeparationPositive : 0 < lengthInKilometers setup.firingSeparation
  flightTimePositive :
    0 < durationInSeconds setup.flightTimeInStarfighterFrame
  enemyVelocitySubluminal :
    |axialVelocityReadout LengthUnit.kilometers TimeUnit.seconds
        (setup.velocityInFrame .enemyShip .starfighterRest)| <
      vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds
  missileVelocityInEnemyFrameSubluminal :
    |axialVelocityReadout LengthUnit.kilometers TimeUnit.seconds
        (setup.velocityInFrame .missile .enemyRest)| <
      vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds
  missileVelocityInStarfighterFrameSubluminal :
    |axialVelocityReadout LengthUnit.kilometers TimeUnit.seconds
        (setup.velocityInFrame .missile .starfighterRest)| <
      vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds

/-! ## Governing special-relativistic and kinematic laws -/

/-!
The collinear Einstein velocity-addition law and uniform-motion interception
law.  If the enemy has velocity `v` in the starfighter frame and the missile
has velocity `u'` in the enemy frame, then its starfighter-frame velocity is
`(v + u') / (1 + v*u'/c^2)`.  The travel law is `speed * time = separation` in
every compatible unit pair.  Neither law contains `55/64`, `31.0 s`, or an
answer label.
-/
structure SatisfiesCollinearRelativisticInterceptLaws
    (setup : RelativisticMissileSetup) : Prop where
  einsteinVelocityAddition :
    ∀ lengthUnit timeUnit,
      axialVelocityReadout lengthUnit timeUnit
          (setup.velocityInFrame .missile .starfighterRest) =
        (axialVelocityReadout lengthUnit timeUnit
              (setup.velocityInFrame .enemyShip .starfighterRest) +
            axialVelocityReadout lengthUnit timeUnit
              (setup.velocityInFrame .missile .enemyRest)) /
          (1 +
            axialVelocityReadout lengthUnit timeUnit
                (setup.velocityInFrame .enemyShip .starfighterRest) *
              axialVelocityReadout lengthUnit timeUnit
                (setup.velocityInFrame .missile .enemyRest) /
              vacuumSpeedOfLightReadout lengthUnit timeUnit ^ 2)
  constantVelocityIntercept :
    ∀ lengthUnit timeUnit,
      axialVelocityReadout lengthUnit timeUnit
            (setup.velocityInFrame .missile .starfighterRest) *
          durationReadout timeUnit setup.flightTimeInStarfighterFrame =
        lengthReadout lengthUnit setup.firingSeparation

/-! ## Derived velocity, displayed answers, and formalization target -/

/-- Missile velocity in the starfighter frame as a dimensionless fraction of `c`. -/
def missileVelocityFractionOfLightInStarfighterFrame
    (setup : RelativisticMissileSetup) : ℝ :=
  axialVelocityReadout LengthUnit.kilometers TimeUnit.seconds
      (setup.velocityInFrame .missile .starfighterRest) /
    vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds

/-!
Einstein addition of `2/5 c` and `7/10 c` gives
`(2/5 + 7/10) / (1 + (2/5)(7/10)) = 55/64`.
-/
lemma missileVelocityFractionOfLight_eq_fiftyFiveOverSixtyFour
    (setup : RelativisticMissileSetup)
    (_problem : MatchesProblemStatement setup)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_laws : SatisfiesCollinearRelativisticInterceptLaws setup) :
    missileVelocityFractionOfLightInStarfighterFrame setup =
      (55 / 64 : ℝ) := by
  have hc := _physical.lightSpeedPositive
  have hv :=
    _laws.einsteinVelocityAddition
      LengthUnit.kilometers TimeUnit.seconds
  rw [_problem.enemyVelocityIsPointFourC,
    _problem.missileVelocityRelativeToEnemyIsPointSevenC] at hv
  unfold missileVelocityFractionOfLightInStarfighterFrame
  field_simp [ne_of_gt hc] at hv ⊢
  nlinarith

/-- Labels of the four time choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Seconds printed beside each displayed answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 189 / 10
  | .B => 142 / 5
  | .C => 138 / 5
  | .D => 31

/-!
A displayed answer is selected by being strictly closer than every other
choice.  This accommodates the textbook use of the rounded value
`c ≈ 3.00 * 10^5 km/s` while the physical model retains Physlib's exact
vacuum light speed.
-/
def IsUniqueClosestAnswerChoice
    (actualSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualSeconds - choice.seconds| <
      |actualSeconds - other.seconds|

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The launch separation and the derived starfighter-frame missile velocity give
the exact Physlib-calibrated flight-time formula.  This is a consequence of
the governing laws, not a premise or a definition of the elapsed time.
-/
lemma missileFlightTimeInSeconds_exact
    (setup : RelativisticMissileSetup)
    (_problem : MatchesProblemStatement setup)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_laws : SatisfiesCollinearRelativisticInterceptLaws setup) :
    durationInSeconds setup.flightTimeInStarfighterFrame =
      lengthInKilometers setup.firingSeparation /
        ((55 / 64 : ℝ) *
          vacuumSpeedOfLightReadout
            LengthUnit.kilometers TimeUnit.seconds) := by
  have hc := _physical.lightSpeedPositive
  have hvFraction :=
    missileVelocityFractionOfLight_eq_fiftyFiveOverSixtyFour
      setup _problem _physical _laws
  unfold missileVelocityFractionOfLightInStarfighterFrame at hvFraction
  have hv := (div_eq_iff (ne_of_gt hc)).mp hvFraction
  have htravel :=
    _laws.constantVelocityIntercept
      LengthUnit.kilometers TimeUnit.seconds
  rw [hv] at htravel
  apply (eq_div_iff ?_).2
  · simpa [durationInSeconds, lengthInKilometers, mul_comm] using htravel
  · positivity

/-!
In the starfighter frame the missile moves at `55/64 c`.  Crossing the stated
`8.00 * 10^6 km` therefore takes about `31 s`, uniquely selecting recorded
answer D (`31.0 s`).

This formalizes `thm:physics:phyx_mini_0512:target`.
-/
theorem missileFlightTime_matches_recordedAnswerD
    (setup : RelativisticMissileSetup)
    (_frames : MatchesNamedRestFrames setup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesSuppliedFigure setup.figure)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_laws : SatisfiesCollinearRelativisticInterceptLaws setup) :
    durationInSeconds setup.flightTimeInStarfighterFrame =
        (8 * 10 ^ 6 : ℝ) /
          ((55 / 64 : ℝ) *
            vacuumSpeedOfLightReadout
              LengthUnit.kilometers TimeUnit.seconds) ∧
      IsUniqueClosestAnswerChoice
        (durationInSeconds setup.flightTimeInStarfighterFrame)
        recordedAnswerChoice := by
  have hc :
      vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds =
        (299792458 / 1000 : ℝ) := by
    norm_num [vacuumSpeedOfLightReadout, DimSpeed.speedOfLight,
      CarriesDimension.toDimensionful_apply_apply, LengthUnit.kilometers,
      LengthUnit.scale, LengthUnit.meters, LengthUnit.div_eq_val,
      TimeUnit.seconds, UnitChoices.SI, UnitChoices.dimScale,
      NNReal.smul_def, NNReal.toReal]
  constructor
  · rw [missileFlightTimeInSeconds_exact setup _problem _physical _laws,
      _problem.firingSeparationKilometers]
  · intro other hother
    rw [missileFlightTimeInSeconds_exact setup _problem _physical _laws,
      _problem.firingSeparationKilometers, hc]
    cases other with
    | A => norm_num [recordedAnswerChoice, AnswerChoice.seconds]
    | B => norm_num [recordedAnswerChoice, AnswerChoice.seconds]
    | C => norm_num [recordedAnswerChoice, AnswerChoice.seconds]
    | D => exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0512
