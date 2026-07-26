import Mathlib
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.SpaceAndTime.Space.Module
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0513

open Dimension

/-!
# Relativistic appearance of the Denebian Empire marking

The primary figure labels the Empire ellipse's vertical major-axis diameter by
`a` and its horizontal minor-axis diameter by `b`.  The proper ratio is
`a / b = 1.40`.  Neither the text nor the figure specifies the direction of
the ship's velocity relative to those axes.  The model therefore keeps the
velocity direction unknown and states the answer in terms of the ellipse's
proper diameters parallel and perpendicular to that direction.

Lengths and speed are dimensionful Physlib quantities.  Real scalars below are
explicit unit readouts, dimensionless fractions of the vacuum speed of light,
and the dimensionless values printed with the answer choices.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Scalar readout of a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : DimSpeed) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Physlib's exact vacuum speed of light in selected length and time units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- The two fleets distinguished in the problem and its primary figure. -/
inductive StarshipFaction where
  | federation
  | empire
  deriving DecidableEq, Repr

/-- Rest-frame marking shapes displayed on the two ships. -/
inductive MarkingShape where
  | circle
  | ellipse
  deriving DecidableEq, Repr

/-- Axis labels printed next to the Empire ellipse in the primary figure. -/
inductive FigureAxis where
  | a
  | b
  deriving DecidableEq, Repr

/-- Directions in the plane of the marking as drawn in the primary figure. -/
inductive FigureDirection where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Geometric roles played by the two principal axes of an ellipse. -/
inductive PrincipalAxisRole where
  | major
  | minor
  deriving DecidableEq, Repr

/-- The observer is modeled in the inertial frame relative to which speed is measured. -/
inductive ObserverFrameKind where
  | inertial
  deriving DecidableEq, Repr

/-!
Physical quantities and figure labels for the marking experiment.

The observed diameters and relative speed are unknowns.  In particular, this
structure does not assign the requested speed or identify an answer choice.
-/
structure StarshipMarkingSetup where
  markingShape : StarshipFaction → MarkingShape
  observerFrame : ObserverFrameKind
  axisDirection : FigureAxis → FigureDirection
  axisSpatialDirection : FigureAxis → Space.Direction 2
  axisRole : FigureAxis → PrincipalAxisRole
  empireProperDiameter : Space.Direction 2 → LengthQuantity
  empireObservedDiameter : Space.Direction 2 → LengthQuantity
  empireVelocityDirection : Space.Direction 2
  empireTransverseDirection : Space.Direction 2
  empireSpeedRelativeToObserver : DimSpeed

/-- Dimensionless speed `β = v/c`, read in common SI length and time units. -/
def speedFractionOfLight (setup : StarshipMarkingSetup) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds
      setup.empireSpeedRelativeToObserver /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-!
Scenario and primary-figure readouts.  The figure identifies the Federation
marking as a circle and the Empire marking as an ellipse; its `a` arrow is
vertical and major, while `b` is horizontal and minor.  The stated factor
`1.40` is represented exactly as `7 / 5` in every length unit.
-/
structure MatchesScenarioAndPrimaryFigure
    (setup : StarshipMarkingSetup) : Prop where
  federationMarkingIsCircle : setup.markingShape .federation = .circle
  empireMarkingIsEllipse : setup.markingShape .empire = .ellipse
  observerIsInertial : setup.observerFrame = .inertial
  axisAIsVertical : setup.axisDirection .a = .vertical
  axisBIsHorizontal : setup.axisDirection .b = .horizontal
  axisAIsMajor : setup.axisRole .a = .major
  axisBIsMinor : setup.axisRole .b = .minor
  figureAxesPerpendicular :
    @inner ℝ (Space 2) _
        (setup.axisSpatialDirection .a).unit
        (setup.axisSpatialDirection .b).unit = 0
  properMajorToMinorRatio :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.empireProperDiameter (setup.axisSpatialDirection .a)) =
        (7 / 5 : ℝ) *
          lengthReadout unit
            (setup.empireProperDiameter (setup.axisSpatialDirection .b))

/-- Positivity and subluminal conditions for the physical configuration. -/
structure HasPhysicalMarkingParameters
    (setup : StarshipMarkingSetup) : Prop where
  properDiametersPositive : ∀ direction,
    0 < lengthReadout LengthUnit.meters
      (setup.empireProperDiameter direction)
  observedDiametersPositive : ∀ direction,
    0 < lengthReadout LengthUnit.meters
      (setup.empireObservedDiameter direction)
  velocityAndTransverseDirectionsPerpendicular :
    @inner ℝ (Space 2) _
        setup.empireVelocityDirection.unit
        setup.empireTransverseDirection.unit = 0
  speedNonnegative : 0 ≤ speedFractionOfLight setup
  speedSubluminal : speedFractionOfLight setup < 1

/-!
The governing special-relativistic length-contraction law.  The diameter along
the unknown velocity direction is divided by Physlib's Lorentz factor `γ(β)`,
while a perpendicular diameter is invariant.  These are general laws involving
the unknown `β` and unknown orientation, not a problem-specific answer formula.
-/
structure ObeysSpecialRelativisticLengthContraction
    (setup : StarshipMarkingSetup) : Prop where
  longitudinalDiameterLaw :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.empireObservedDiameter setup.empireVelocityDirection) =
        lengthReadout unit
            (setup.empireProperDiameter setup.empireVelocityDirection) /
          LorentzGroup.γ (speedFractionOfLight setup)
  transverseDiameterInvariant :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.empireObservedDiameter setup.empireTransverseDirection) =
        lengthReadout unit
          (setup.empireProperDiameter setup.empireTransverseDirection)

/-!
The condition posed in the question: an observer can confuse the Empire
marking with the Federation circle when every observed directional diameter
has the same readout.  This is an observational condition, not a speed or
velocity-direction assignment.
-/
structure AppearsCircularToObserver
    (setup : StarshipMarkingSetup) : Prop where
  observedDiametersIndependentOfDirection :
    ∀ (unit : LengthUnit) (direction₁ direction₂ : Space.Direction 2),
      lengthReadout unit (setup.empireObservedDiameter direction₁) =
        lengthReadout unit (setup.empireObservedDiameter direction₂)

/-- Labels of the four speed choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless coefficient of `c` displayed beside each answer choice. -/
def displayedSpeedFraction : AnswerChoice → ℝ
  | .A => 41 / 50
  | .B => 33 / 50
  | .C => 19 / 20
  | .D => 7 / 10

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/--
If the Empire marking appears circular, the Lorentz-contraction law determines
the speed from the ratio of its proper diameter transverse to the velocity to
its proper diameter along the velocity.  This orientation-dependent relation
is the strongest conclusion supported by the source: the primary figure does
not say that the velocity is parallel to the major axis.  Consequently the
recorded choice D above is metadata and is not selected by this theorem.

Blueprint: `thm:physics:phyx_mini_0513:target`.
-/
theorem empireShipSpeedForCircularMarking
    (setup : StarshipMarkingSetup)
    (hFigure : MatchesScenarioAndPrimaryFigure setup)
    (hPhysical : HasPhysicalMarkingParameters setup)
    (hContraction : ObeysSpecialRelativisticLengthContraction setup)
    (hCircular : AppearsCircularToObserver setup) :
    speedFractionOfLight setup =
      Real.sqrt
        (1 -
          (lengthReadout LengthUnit.meters
                (setup.empireProperDiameter setup.empireTransverseDirection) /
              lengthReadout LengthUnit.meters
                (setup.empireProperDiameter setup.empireVelocityDirection)) ^ 2) := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0513
