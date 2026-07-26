import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Relativistic missile flight time

An enemy spacecraft approaches a starfighter at `0.400 c` in the
starfighter's rest frame. It launches a missile toward the starfighter at
`0.700 c` in the enemy's rest frame. At launch the two spacecraft are
`8.00 * 10^6 km` apart in the starfighter frame.

Lengths, elapsed times, and signed axial velocities are represented by
Physlib dimensionful quantities. Real numbers below are only readouts in
named units, dimensionless fractions of the speed of light, qualitative
figure ranks, or displayed answer values. Positive velocity points from the
enemy toward the starfighter, matching the left-to-right orientation of the
supplied figure.

Assumption/target split:

* governing laws: named rest-frame behavior, collinear Einstein velocity
  addition, and constant-velocity travel from the firing point to the target;
* previous-part results: none;
* figure/data readouts: the three left-to-right bodies, labels and connectors,
  `0.400 c`, `0.700 c`, and `8.00 * 10^6 km` in their stated frames;
* target conclusions: the derived missile speed `55/64 c`, the exact elapsed
  time in the starfighter frame, and unique selection of choice A (`31.0 s`).
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0607

open Dimension

/-! ## Dimensionful quantities and calibrated scalar readouts -/

/-- A nonnegative, unit-independent physical separation. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent elapsed physical time. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-!
A signed one-dimensional physical velocity. Physlib's `DimSpeed` is
nonnegative, whereas the common flight axis here needs an orientation.
-/
abbrev AxialVelocity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a physical length in a named length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read an elapsed physical time in a named time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed axial velocity in compatible length and time units. -/
def axialVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : AxialVelocity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read Physlib's exact dimensionful vacuum speed of light in named units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Kilometer readout of the separation at the firing event. -/
def lengthInKilometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.kilometers length

/-- Second readout of the elapsed time requested by the problem. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-! ## Reference frames, bodies, directions, and figure vocabulary -/

/-- The two inertial rest frames named in the scenario. -/
inductive InertialFrame where
  | enemyRest
  | starfighterRest
  deriving DecidableEq, Repr

/-- The three physical bodies visible from left to right in image 607. -/
inductive BodyLabel where
  | enemyShip
  | missile
  | starfighter
  deriving DecidableEq, Repr

/-! `towardStarfighter` is the positive direction on the common flight axis. -/
inductive AxialDirection where
  | towardEnemy
  | towardStarfighter
  deriving DecidableEq, Repr

/-- The two text labels printed under the spacecraft. -/
inductive PrintedFigureLabel where
  | enemy
  | starfighter
  deriving DecidableEq, Repr

/-- The pale segment and green trajectory arrow visible in the raster. -/
inductive ConnectorStyle where
  | paleGreenLine
  | greenTrajectoryArrow
  deriving DecidableEq, Repr

/-!
Qualitative evidence extracted from the supplied image. Natural-number ranks
represent only left-to-right drawing order, not physical coordinates.
-/
structure SpaceshipMissileFigure where
  shows : BodyLabel → Bool
  leftToRightRank : BodyLabel → ℕ
  hasPrintedLabel : BodyLabel → Bool
  printedLabelTarget : PrintedFigureLabel → BodyLabel
  connectorFrom : ConnectorStyle → BodyLabel
  connectorTo : ConnectorStyle → BodyLabel

/-!
Independent physical observables for the scenario. The missile velocity in
the starfighter frame and its flight time are unknown physical quantities;
neither is defined from a displayed answer.
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

/-! ## Scenario data, primary-image evidence, and physical domain -/

/-- The frame labels denote the rest frames of their defining spacecraft. -/
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
Numerical and directional information stated in the prose. This gives no
starfighter-frame missile velocity and no flight-time result.
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
        (2 / 5 : ℝ) * vacuumSpeedOfLightReadout lengthUnit timeUnit
  missileVelocityRelativeToEnemyIsPointSevenC :
    ∀ lengthUnit timeUnit,
      axialVelocityReadout lengthUnit timeUnit
          (setup.velocityInFrame .missile .enemyRest) =
        (7 / 10 : ℝ) * vacuumSpeedOfLightReadout lengthUnit timeUnit

/-!
Facts visible in image 607: enemy, missile, and starfighter appear from left
to right; only the spacecraft have text labels; the pale segment joins the
enemy to the missile; and the green arrow points from missile to starfighter.
The image supplies no quantitative spatial scale.
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
  paleLineStartsAtEnemy : figure.connectorFrom .paleGreenLine = .enemyShip
  paleLineEndsAtMissile : figure.connectorTo .paleGreenLine = .missile
  trajectoryStartsAtMissile :
    figure.connectorFrom .greenTrajectoryArrow = .missile
  trajectoryPointsToStarfighter :
    figure.connectorTo .greenTrajectoryArrow = .starfighter

/-!
Positivity and subluminality exclude degenerate models without assigning a
numerical answer to either unknown observable.
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
The collinear Einstein velocity-addition law and the constant-velocity travel
law. If the enemy has velocity `v` in the starfighter frame and the missile
has velocity `u'` in the enemy frame, the missile velocity in the starfighter
frame is `(v + u') / (1 + v*u'/c^2)`. Neither law contains `55/64`, `31.0 s`,
or an answer label.
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

/-! ## Derived observables, displayed answers, and current target -/

/-- Missile velocity in the starfighter frame as a dimensionless ratio to `c`. -/
def missileVelocityFractionOfLightInStarfighterFrame
    (setup : RelativisticMissileSetup) : ℝ :=
  axialVelocityReadout LengthUnit.kilometers TimeUnit.seconds
      (setup.velocityInFrame .missile .starfighterRest) /
    vacuumSpeedOfLightReadout LengthUnit.kilometers TimeUnit.seconds

/-! Einstein addition of `2/5 c` and `7/10 c` gives `55/64 c`. -/
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

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Seconds printed beside each displayed answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 31
  | .B => 152 / 5
  | .C => 331 / 10
  | .D => 164 / 5

/-!
A displayed choice matches when it is strictly closer than every alternative.
This states the multiple-choice interpretation without asserting the rounded
`31.0 s` display as an exact equality to the physical elapsed time.
-/
def IsUniqueClosestAnswerChoice
    (actualSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualSeconds - choice.seconds| <
      |actualSeconds - other.seconds|

/-- Choice A is the answer label recorded by the dataset, not a premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/-!
The given separation and derived missile velocity determine the exact
Physlib-calibrated elapsed-time expression. This is derived, not assumed.
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
In the starfighter frame the missile travels at `55/64 c`. Crossing the stated
`8.00 * 10^6 km` therefore takes approximately `31.0 s`, uniquely selecting
choice A.

Blueprint label: `thm:physics:phyx_mini_0607:target`.
-/
theorem problem_phyx_mini_0607
    (setup : RelativisticMissileSetup)
    (_frames : MatchesNamedRestFrames setup)
    (_problem : MatchesProblemStatement setup)
    (_figure : MatchesSuppliedFigure setup.figure)
    (_physical : HasPhysicalRelativisticParameters setup)
    (_laws : SatisfiesCollinearRelativisticInterceptLaws setup) :
    missileVelocityFractionOfLightInStarfighterFrame setup =
        (55 / 64 : ℝ) ∧
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
  refine ⟨missileVelocityFractionOfLight_eq_fiftyFiveOverSixtyFour
      setup _problem _physical _laws, ?_, ?_⟩
  · rw [missileFlightTimeInSeconds_exact setup _problem _physical _laws,
      _problem.firingSeparationKilometers]
  · intro other hother
    rw [missileFlightTimeInSeconds_exact setup _problem _physical _laws,
      _problem.firingSeparationKilometers, hc]
    cases other with
    | A => exact (hother rfl).elim
    | B => norm_num [recordedAnswerChoice, AnswerChoice.seconds]
    | C => norm_num [recordedAnswerChoice, AnswerChoice.seconds]
    | D => norm_num [recordedAnswerChoice, AnswerChoice.seconds]

end PhyXMiniProblems.ProblemPhyXMini0607
