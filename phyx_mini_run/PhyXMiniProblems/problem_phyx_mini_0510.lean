import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0510

open Dimension

/-!
# Relativistic velocity of a robot probe

The Earth frame `S` and the spaceship frame `S'` have relative velocity
`0.900 c` along their common positive horizontal axis.  The robot probe moves
in that same direction at `0.700 c` as measured in `S'`.  The requested
quantity is the probe's velocity in `S`.

Velocities below are signed, unit-independent Physlib quantities.  Real
numbers are used only for dimensionless readouts in units of the exact vacuum
speed of light, for the displayed answer choices, and for rounding.
-/

/-- A signed physical velocity carrying length-per-time dimension. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a signed physical velocity in selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : VelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Physlib's exact vacuum speed of light in the selected units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- The dimensionless signed ratio `v / c`, evaluated in SI units. -/
def velocityInLightSpeedUnits (velocity : VelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-- Reference-frame labels printed in the figure. -/
inductive ReferenceFrameLabel where
  | earthS
  | spaceshipSPrime
  deriving DecidableEq, Repr

/-- Coordinate-axis labels printed in the two frames. -/
inductive AxisLabel where
  | x
  | y
  | xPrime
  | yPrime
  deriving DecidableEq, Repr

/-- Physical objects distinguished by the primary figure. -/
inductive FigureObjectLabel where
  | earth
  | scoutship
  | spaceship
  | robotSpaceProbe
  deriving DecidableEq, Repr

/-- The common rightward direction of all three velocity arrows. -/
inductive AxialDirection where
  | positiveCommonHorizontalAxis
  deriving DecidableEq, Repr

/-- Multiple-choice labels from the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed candidate values, as dimensionless multiples of `c`. -/
def answerChoiceInLightSpeedUnits : AnswerChoice → ℝ
  | .A => 937 / 1000
  | .B => 951 / 1000
  | .C => 966 / 1000
  | .D => 982 / 1000

/-!
All named labels and physical velocities in the scenario.  In particular,
`probeVelocityInEarthFrame` is an unknown quantity: no field assigns it a
numerical value or an answer choice.
-/
structure RelativisticProbeSetup where
  earthFrame : ReferenceFrameLabel
  spaceshipFrame : ReferenceFrameLabel
  earthHorizontalAxis : AxisLabel
  earthVerticalAxis : AxisLabel
  spaceshipHorizontalAxis : AxisLabel
  spaceshipVerticalAxis : AxisLabel
  earthObject : FigureObjectLabel
  scoutshipObject : FigureObjectLabel
  spaceshipObject : FigureObjectLabel
  probeObject : FigureObjectLabel
  spaceshipMotionDirection : AxialDirection
  scoutshipMotionDirection : AxialDirection
  probeMotionDirection : AxialDirection
  spaceshipVelocityInEarthFrame : VelocityQuantity
  probeVelocityInSpaceshipFrame : VelocityQuantity
  probeVelocityInEarthFrame : VelocityQuantity
  scoutshipVelocityInEarthFrame : VelocityQuantity

/-- Qualitative labels, axes, and rightward collinearity read from the figure. -/
def MatchesFigureGeometry (setup : RelativisticProbeSetup) : Prop :=
  setup.earthFrame = .earthS ∧
    setup.spaceshipFrame = .spaceshipSPrime ∧
    setup.earthHorizontalAxis = .x ∧
    setup.earthVerticalAxis = .y ∧
    setup.spaceshipHorizontalAxis = .xPrime ∧
    setup.spaceshipVerticalAxis = .yPrime ∧
    setup.earthObject = .earth ∧
    setup.scoutshipObject = .scoutship ∧
    setup.spaceshipObject = .spaceship ∧
    setup.probeObject = .robotSpaceProbe ∧
    setup.spaceshipMotionDirection = .positiveCommonHorizontalAxis ∧
    setup.scoutshipMotionDirection = .positiveCommonHorizontalAxis ∧
    setup.probeMotionDirection = .positiveCommonHorizontalAxis

/-!
The two numerical givens used by the question: the spaceship moves at
`0.900 c` in `S`, and the probe moves at `0.700 c` in `S'`.
-/
def MatchesProblemReadouts (setup : RelativisticProbeSetup) : Prop :=
  velocityInLightSpeedUnits setup.spaceshipVelocityInEarthFrame = 9 / 10 ∧
    velocityInLightSpeedUnits setup.probeVelocityInSpaceshipFrame = 7 / 10

/-!
The separate yellow scoutship is labeled `v_x = 0.950 c` in the primary
figure.  It is retained as an auxiliary figure readout and is not used in the
probe's velocity-transformation law.
-/
def MatchesAuxiliaryScoutshipReadout
    (setup : RelativisticProbeSetup) : Prop :=
  velocityInLightSpeedUnits setup.scoutshipVelocityInEarthFrame = 19 / 20

/-!
The governing one-dimensional special-relativistic velocity-addition law,
written in normalized variables `beta = v / c`:

`beta = (beta_u + beta') / (1 + beta_u * beta')`.

This relates the still-unknown Earth-frame probe velocity to the two given
velocities; it does not assert its numerical value or select an answer choice.
-/
def ObeysCollinearRelativisticVelocityAddition
    (setup : RelativisticProbeSetup) : Prop :=
  velocityInLightSpeedUnits setup.probeVelocityInEarthFrame =
    (velocityInLightSpeedUnits setup.spaceshipVelocityInEarthFrame +
      velocityInLightSpeedUnits setup.probeVelocityInSpaceshipFrame) /
      (1 + velocityInLightSpeedUnits setup.spaceshipVelocityInEarthFrame *
        velocityInLightSpeedUnits setup.probeVelocityInSpaceshipFrame)

/--
`value` rounds to `displayed` to the nearest thousandth, with a half-open
interval fixing the convention at exact ties.
-/
def RoundsToNearestThousandth (value displayed : ℝ) : Prop :=
  displayed - 1 / 2000 ≤ value ∧ value < displayed + 1 / 2000

/--
The probe's exact Earth-frame velocity is `(160 / 163) c`; consequently its
three-decimal display is `0.982 c`, answer choice D.

Blueprint label: `thm:physics:phyx_mini_0510:target`.
-/
theorem probeVelocityInEarthFrame_eq_choiceD
    (setup : RelativisticProbeSetup)
    (hFigure : MatchesFigureGeometry setup)
    (hProblem : MatchesProblemReadouts setup)
    (hScoutship : MatchesAuxiliaryScoutshipReadout setup)
    (hAddition : ObeysCollinearRelativisticVelocityAddition setup) :
    velocityInLightSpeedUnits setup.probeVelocityInEarthFrame = 160 / 163 ∧
      RoundsToNearestThousandth
        (velocityInLightSpeedUnits setup.probeVelocityInEarthFrame)
        (answerChoiceInLightSpeedUnits .D) := by
  rcases hProblem with ⟨hSpaceship, hProbe⟩
  norm_num [ObeysCollinearRelativisticVelocityAddition, hSpaceship, hProbe] at hAddition
  refine ⟨hAddition, ?_⟩
  norm_num [RoundsToNearestThousandth, answerChoiceInLightSpeedUnits, hAddition]

end PhyXMiniProblems.ProblemPhyXMini0510
