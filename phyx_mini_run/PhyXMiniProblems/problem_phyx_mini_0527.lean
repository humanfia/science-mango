import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0527

open Dimension

/-!
# Relativistic overtaking speed of two spacecraft

In the Earth frame `S`, an enemy spacecraft and a galactic patrol spacecraft
move along the common positive horizontal axis at `0.800 c` and `0.900 c`,
respectively.  Earth observers therefore report a closing rate of `0.100 c`.
The requested speed is measured in the patrol crew's frame `S'`, so it is the
magnitude of a Lorentz-transformed velocity rather than the Earth-frame
difference of the two velocities.

Signed velocities and nonnegative speeds are unit-independent Physlib
quantities carrying length-per-time dimension.  Real numbers occur only as
unit readouts, dimensionless ratios to the vacuum speed of light, and displayed
answer values.
-/

/-! ## Dimensionful velocities, speeds, and scalar readouts -/

/-- A signed one-dimensional physical velocity. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative physical speed, independent of a choice of units. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a signed velocity in selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a nonnegative speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Physlib's exact vacuum speed of light in the selected units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  signedVelocityReadout lengthUnit timeUnit DimSpeed.speedOfLight

/-- Dimensionless signed velocity in units of the vacuum speed of light. -/
def velocityInLightSpeedUnits (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-- Dimensionless nonnegative speed in units of the vacuum speed of light. -/
def speedInLightSpeedUnits (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-! ## Frames, objects, axes, and primary-image labels -/

/-- The two inertial-frame labels printed in the supplied figure. -/
inductive ReferenceFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Repr

/-- The horizontal coordinate-axis labels printed in the two panels. -/
inductive CoordinateAxisLabel where
  | x
  | xPrime
  deriving DecidableEq, Repr

/-- Physical objects explicitly shown in the figure. -/
inductive FigureObjectLabel where
  | earth
  | galacticPatrolSpacecraft
  | enemySpacecraft
  deriving DecidableEq, Repr

/-- Velocity-vector labels printed above the two spacecraft. -/
inductive VelocityArrowLabel where
  | u
  | v
  deriving DecidableEq, Repr

/-- Orientation along the common horizontal motion axis. -/
inductive AxialDirection where
  | positive
  | negative
  deriving DecidableEq, Repr

/-!
Qualitative evidence from `phyx_data/test_image/527.png`.  The image has a
left `S,x` panel containing Earth and the patrol craft and a right `S',x'`
panel containing the enemy craft.  Both printed velocity arrows point right.
-/
structure SpacecraftPursuitFigure where
  leftFrameLabel : ReferenceFrameLabel
  rightFrameLabel : ReferenceFrameLabel
  leftHorizontalAxisLabel : CoordinateAxisLabel
  rightHorizontalAxisLabel : CoordinateAxisLabel
  objectPanel : FigureObjectLabel → ReferenceFrameLabel
  velocityArrowObject : VelocityArrowLabel → FigureObjectLabel
  velocityArrowDirection : VelocityArrowLabel → AxialDirection

/-!
All physical quantities in the pursuit problem.  In particular,
`enemyVelocityInPatrolFrame` and `patrolMeasuredOvertakingSpeed` are unknown
observables: no field assigns either one a numerical value or an answer label.
-/
structure SpacecraftPursuitSetup where
  figure : SpacecraftPursuitFigure
  earthFrame : ReferenceFrameLabel
  patrolCrewFrame : ReferenceFrameLabel
  enemyVelocityInEarthFrame : SignedVelocityQuantity
  patrolVelocityInEarthFrame : SignedVelocityQuantity
  earthMeasuredOvertakingSpeed : SpeedQuantity
  enemyVelocityInPatrolFrame : SignedVelocityQuantity
  patrolMeasuredOvertakingSpeed : SpeedQuantity

/-! ## Scenario, figure/data readouts, and governing physics -/

/-- Qualitative frame, object, axis, and arrow information from the figure. -/
def MatchesScenarioAndFigure (setup : SpacecraftPursuitSetup) : Prop :=
  setup.earthFrame = .S ∧
    setup.patrolCrewFrame = .SPrime ∧
    setup.figure.leftFrameLabel = .S ∧
    setup.figure.rightFrameLabel = .SPrime ∧
    setup.figure.leftHorizontalAxisLabel = .x ∧
    setup.figure.rightHorizontalAxisLabel = .xPrime ∧
    setup.figure.objectPanel .earth = .S ∧
    setup.figure.objectPanel .galacticPatrolSpacecraft = .S ∧
    setup.figure.objectPanel .enemySpacecraft = .SPrime ∧
    setup.figure.velocityArrowObject .u = .galacticPatrolSpacecraft ∧
    setup.figure.velocityArrowObject .v = .enemySpacecraft ∧
    setup.figure.velocityArrowDirection .u = .positive ∧
    setup.figure.velocityArrowDirection .v = .positive

/-!
The three numerical readouts stated in the problem.  These concern only
Earth-frame quantities: enemy speed `0.800 c`, patrol speed `0.900 c`, and
the Earth-observed closing rate `0.100 c`.
-/
def MatchesProblemReadouts (setup : SpacecraftPursuitSetup) : Prop :=
  velocityInLightSpeedUnits setup.enemyVelocityInEarthFrame = (4 / 5 : ℝ) ∧
    velocityInLightSpeedUnits setup.patrolVelocityInEarthFrame = (9 / 10 : ℝ) ∧
    speedInLightSpeedUnits setup.earthMeasuredOvertakingSpeed = (1 / 10 : ℝ)

/-- Positivity, ordering, and subluminality of the stated Earth-frame data. -/
def HasPhysicalPursuitParameters (setup : SpacecraftPursuitSetup) : Prop :=
  0 < vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds ∧
    0 < velocityInLightSpeedUnits setup.enemyVelocityInEarthFrame ∧
    velocityInLightSpeedUnits setup.enemyVelocityInEarthFrame <
      velocityInLightSpeedUnits setup.patrolVelocityInEarthFrame ∧
    velocityInLightSpeedUnits setup.patrolVelocityInEarthFrame < 1 ∧
    0 < speedInLightSpeedUnits setup.earthMeasuredOvertakingSpeed ∧
    speedInLightSpeedUnits setup.earthMeasuredOvertakingSpeed < 1

/-!
Ordinary same-frame kinematics for the Earth observers: because both craft
move right and the patrol is faster, their reported closing speed is `u - v`.
This preserves the separately stated `0.100 c` observation without using the
patrol-frame target.
-/
def ObeysEarthFrameClosingRate (setup : SpacecraftPursuitSetup) : Prop :=
  speedInLightSpeedUnits setup.earthMeasuredOvertakingSpeed =
    velocityInLightSpeedUnits setup.patrolVelocityInEarthFrame -
      velocityInLightSpeedUnits setup.enemyVelocityInEarthFrame

/-!
The governing one-dimensional Lorentz velocity transformation

`beta'_enemy = (beta_enemy - beta_patrol) /
  (1 - beta_patrol * beta_enemy)`.

Its left-hand side is still an unknown patrol-frame velocity, and this law
contains no numerical patrol-frame speed or answer choice.
-/
def ObeysCollinearRelativisticVelocityTransformation
    (setup : SpacecraftPursuitSetup) : Prop :=
  velocityInLightSpeedUnits setup.enemyVelocityInPatrolFrame =
    (velocityInLightSpeedUnits setup.enemyVelocityInEarthFrame -
      velocityInLightSpeedUnits setup.patrolVelocityInEarthFrame) /
      (1 - velocityInLightSpeedUnits setup.patrolVelocityInEarthFrame *
        velocityInLightSpeedUnits setup.enemyVelocityInEarthFrame)

/-!
Operational meaning of the requested speed: the patrol crew reports the
nonnegative magnitude of the enemy's signed velocity in the patrol frame.
-/
def PatrolMeasuredSpeedIsRelativeVelocityMagnitude
    (setup : SpacecraftPursuitSetup) : Prop :=
  speedInLightSpeedUnits setup.patrolMeasuredOvertakingSpeed =
    |velocityInLightSpeedUnits setup.enemyVelocityInPatrolFrame|

/-! ## Multiple-choice target -/

/-- Labels of the four choices printed in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed candidate speeds, as dimensionless multiples of `c`. -/
def answerChoiceInLightSpeedUnits : AnswerChoice → ℝ
  | .A => 253 / 1000
  | .B => 407 / 1000
  | .C => 331 / 1000
  | .D => 357 / 1000

/-- Nearest-thousandth agreement, using a half-open convention at ties. -/
def RoundsToNearestThousandth (value displayed : ℝ) : Prop :=
  displayed - 1 / 2000 ≤ value ∧ value < displayed + 1 / 2000

/-!
The transformed enemy velocity is `-(5/14)c`, so the patrol crew measures an
overtaking speed of `(5/14)c`.  This rounds to `0.357c`, answer choice D.

Blueprint label: `thm:physics:phyx_mini_0527:target`.
-/
theorem patrolCrewMeasuredOvertakingSpeed_eq_choiceD
    (setup : SpacecraftPursuitSetup)
    (hFigure : MatchesScenarioAndFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalPursuitParameters setup)
    (hEarthClosing : ObeysEarthFrameClosingRate setup)
    (hLorentz : ObeysCollinearRelativisticVelocityTransformation setup)
    (hMagnitude : PatrolMeasuredSpeedIsRelativeVelocityMagnitude setup) :
    speedInLightSpeedUnits setup.patrolMeasuredOvertakingSpeed = (5 / 14 : ℝ) ∧
      RoundsToNearestThousandth
        (speedInLightSpeedUnits setup.patrolMeasuredOvertakingSpeed)
        (answerChoiceInLightSpeedUnits .D) := by
  rcases hReadouts with ⟨hEnemy, hPatrol, _⟩
  unfold ObeysCollinearRelativisticVelocityTransformation at hLorentz
  rw [hEnemy, hPatrol] at hLorentz
  norm_num at hLorentz
  unfold PatrolMeasuredSpeedIsRelativeVelocityMagnitude at hMagnitude
  rw [hLorentz] at hMagnitude
  norm_num at hMagnitude
  constructor
  · exact hMagnitude
  · rw [hMagnitude]
    unfold RoundsToNearestThousandth answerChoiceInLightSpeedUnits
    norm_num

end PhyXMiniProblems.ProblemPhyXMini0527
