import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Water pressure required to lift a piston

A `100 kg` piston of cross-sectional area `0.01 m²` initially rests on stops
above water.  Atmospheric pressure `P₀ = 100 kPa` acts on its upper face and
gravity acts downward.  At incipient lift, the upward water-pressure force
balances the atmospheric-pressure force together with the piston's weight.

Pressure and area use Physlib's unit-independent dimensional quantities.  The
piston mass and gravitational acceleration are also dimension-tagged; real
numbers occur only in explicitly named coherent-SI readouts and in the
displayed answer choices.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0384

open Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A physical absolute pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI square-metre readout of an area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Coherent-SI pascal readout of an absolute pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used by the four displayed answers. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-! ## Apparatus roles and primary-figure information -/

/-- The fluid occupying the cylinder below the piston. -/
inductive CylinderFluid where
  | water
  deriving DecidableEq, Repr

/-- Regions distinguished by the supplied cross-sectional diagram. -/
inductive FigureRegion where
  | abovePiston
  | belowPiston
  deriving DecidableEq, Repr

/-- Vertical direction of a force or acceleration arrow. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The piston's support condition before the water pressure is increased. -/
inductive InitialPistonSupport where
  | restingOnStops
  deriving DecidableEq, Repr

/-- Labels and placements read directly from the primary figure. -/
structure PistonCylinderFigure where
  fluidLabel : String
  externalPressureLabel : String
  gravityLabel : String
  fluidRegion : FigureRegion
  externalPressureRegion : FigureRegion
  gravityArrowDirection : VerticalDirection

/--
The piston/cylinder and the physical quantities relevant at the threshold of
lift.  `liftThresholdWaterPressure` is an unknown physical pressure field; no
definition assigns it the requested numerical value.
-/
structure PistonCylinderSetup where
  fluid : CylinderFluid
  initialPistonSupport : InitialPistonSupport
  figure : PistonCylinderFigure
  pistonCrossSectionalArea : AreaQuantity
  pistonMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  outsideAtmosphericPressureP0 : PressureQuantity
  liftThresholdWaterPressure : PressureQuantity

/-! ## Figure/data readouts and physical conditions -/

/-- The apparatus and labels visible in the source diagram. -/
structure MatchesPrimaryFigure (setup : PistonCylinderSetup) : Prop where
  fluidIsWater : setup.fluid = .water
  pistonInitiallyRestsOnStops :
    setup.initialPistonSupport = .restingOnStops
  waterLabel : setup.figure.fluidLabel = "Water"
  atmosphericPressureLabel : setup.figure.externalPressureLabel = "P₀"
  gravityLabel : setup.figure.gravityLabel = "g"
  waterIsBelowPiston : setup.figure.fluidRegion = .belowPiston
  atmosphereIsAbovePiston :
    setup.figure.externalPressureRegion = .abovePiston
  gravityPointsDownward :
    setup.figure.gravityArrowDirection = .downward

/--
Numerical readouts supplied by the prose, together with the standard
`g = 9.8 m/s²` value used by the recorded multiple-choice calculation.
-/
structure MatchesProblemData (setup : PistonCylinderSetup) : Prop where
  pistonAreaSquareMeters :
    areaInSquareMeters setup.pistonCrossSectionalArea = 1 / 100
  pistonMassKilograms : massInKilograms setup.pistonMass = 100
  atmosphericPressurePascals :
    pressureInPascals setup.outsideAtmosphericPressureP0 = 100000
  terrestrialGravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5

/-- Positivity assumptions selecting the intended physical branch. -/
structure HasPositivePhysicalParameters
    (setup : PistonCylinderSetup) : Prop where
  areaPositive : 0 < areaInSquareMeters setup.pistonCrossSectionalArea
  massPositive : 0 < massInKilograms setup.pistonMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  atmosphericPressurePositive :
    0 < pressureInPascals setup.outsideAtmosphericPressureP0
  waterPressurePositive :
    0 < pressureInPascals setup.liftThresholdWaterPressure

/-! ## Governing incipient-lift law -/

/-- Upward force readout, in newtons, exerted by the water on the piston. -/
def upwardWaterPressureForceInNewtons
    (setup : PistonCylinderSetup) : ℝ :=
  pressureInPascals setup.liftThresholdWaterPressure *
    areaInSquareMeters setup.pistonCrossSectionalArea

/-- Downward force readout, in newtons, due to the outside atmosphere. -/
def downwardAtmosphericForceInNewtons
    (setup : PistonCylinderSetup) : ℝ :=
  pressureInPascals setup.outsideAtmosphericPressureP0 *
    areaInSquareMeters setup.pistonCrossSectionalArea

/-- Downward gravitational force readout, in newtons, on the piston. -/
def pistonWeightInNewtons (setup : PistonCylinderSetup) : ℝ :=
  massInKilograms setup.pistonMass *
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/--
The ideal vertical force balance at the instant the piston loses contact with
the stops.  This governing law includes no numerical value for the unknown
water pressure and no answer-choice label.
-/
def AtIncipientLift (setup : PistonCylinderSetup) : Prop :=
  upwardWaterPressureForceInNewtons setup =
    downwardAtmosphericForceInNewtons setup + pistonWeightInNewtons setup

/-! ## Displayed answers and requested conclusion -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Kilopascal value printed beside each answer label. -/
def answerPressureInKilopascals : AnswerChoice → ℝ
  | .A => 490
  | .B => 198
  | .C => 154
  | .D => 102 / 10

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/--
The absolute water pressure at incipient lift is `198 kPa`, displayed answer
B.  It is the sum of `100 kPa` atmospheric pressure and the `98 kPa` pressure
increment needed to support the piston's weight.

Blueprint label: `thm:physics:phyx_mini_0384:target`.
-/
theorem waterPressureToLiftPiston_eq_198_kPa
    (setup : PistonCylinderSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPositivePhysicalParameters setup)
    (_liftLaw : AtIncipientLift setup) :
    pressureInKilopascals setup.liftThresholdWaterPressure = 198 := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0384
