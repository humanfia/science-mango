import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0951

open Dimension

/-!
# Current required to balance a pivoted conducting bar

A uniform conducting bar extends from the frictionless pivot `a` to its free
end `b`, at `30°` above the positive horizontal axis.  Gravity acts downward,
and a uniform magnetic field points into the page.  Positive current is
oriented from `a` to `b`.

Mass, length, acceleration, magnetic flux density, current, force, and torque
are unit-independent Physlib `Dimensionful` quantities.  Real numbers are used
only for selected-unit readouts, the dimensionless angle, and displayed answer
values.

Assumption/target split:

* governing laws: `W = m g`, the center of mass of a uniform bar is at `L/2`,
  the gravitational and distributed magnetic torque laws about `a`, torque
  addition, uniform-field calibration, and zero net torque;
* previous-part results: none;
* figure/data readouts: endpoints `a` and `b`, the `x` and `y` axes, the
  `theta` arc, field crosses, `m = 0.0120 kg`, `L = 30.0 cm`,
  `B = 0.150 T`, `theta = 30.0°`, and standard `g = 9.80 m/s²`;
* current target conclusions: the solved current formula and the unique
  nearest displayed value `2.26 A`, answer B.

Neither the solved current formula nor any answer-choice value occurs in a
premise structure.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L² T⁻²` of torque. -/
def torqueDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M T⁻¹ C⁻¹` of magnetic flux density. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `C T⁻¹` of electric current. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-!
A signed current relative to the orientation from `a` to `b`.  Its
dimensionful representation keeps current distinct from a bare scalar.
-/
abbrev ElectricCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-!
A signed torque component about the page-normal pivot axis; positive means
counterclockwise in the supplied `xy` view.
-/
abbrev SignedTorqueQuantity : Type :=
  Dimensionful (WithDim torqueDimension ℝ)

/-- Read a physical mass in a selected unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Coherent-SI acceleration readout, in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI magnetic-flux-density readout, in teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  ((fieldMagnitude UnitChoices.SI).val : ℝ)

/-- Coherent-SI signed-current readout, in amperes. -/
def electricCurrentInAmperes (current : ElectricCurrentQuantity) : ℝ :=
  (current UnitChoices.SI).val

/-- Coherent-SI force-magnitude readout, in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Coherent-SI signed-torque readout, in newton metres. -/
def torqueInNewtonMeters (torque : SignedTorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-- Convert a dimensionless degree readout to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Figure labels, directions, and apparatus -/

/-- The two labeled endpoints in the primary figure. -/
inductive BarPoint where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

/-- The two Cartesian axes drawn in the primary figure. -/
inductive CartesianAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Directions in the plane of the supplied figure. -/
inductive InPlaneDirection where
  | positiveX
  | negativeX
  | positiveY
  | negativeY
  deriving DecidableEq, Repr

/-- Directions perpendicular to the page. -/
inductive PageNormalDirection where
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Reference orientation for signed current along the bar. -/
inductive BarCurrentDirection where
  | fromAToB
  | fromBToA
  deriving DecidableEq, Repr

/-- Sense of a torque in the page view. -/
inductive TorqueSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-!
Literal qualitative content transcribed from image `951.png`.  The crosses
encode a field into the page; the diagonal gold segment joins `a` to `b`; and
the angle arc labeled `theta` is measured from the positive `x` axis at `a`.
-/
structure PivotedBarFigure where
  pointShown : BarPoint → Bool
  axisShown : CartesianAxis → Bool
  barFirstEndpoint : BarPoint
  barSecondEndpoint : BarPoint
  angleArcVertex : BarPoint
  thetaLabelShown : Bool
  barAbovePositiveXAxis : Bool
  uniformFieldCrossesShown : Bool
  magneticFieldLabelShown : Bool

/-!
Independent physical quantities describing the pivoted bar.  The current and
all three torques are observables, not definitions made from the requested
answer.
-/
structure PivotedConductingBarSetup where
  figure : PivotedBarFigure
  barMass : MassQuantity
  barLength : LengthQuantity
  centerOfMassDistanceFromA : LengthQuantity
  gravitationalAcceleration : AccelerationMagnitude
  weightMagnitude : ForceMagnitude
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  current : ElectricCurrentQuantity
  gravitationalTorqueAboutA : SignedTorqueQuantity
  magneticTorqueAboutA : SignedTorqueQuantity
  netTorqueAboutA : SignedTorqueQuantity
  barAngleAboveHorizontalRadians : ℝ
  magneticField : Electromagnetism.MagneticField 3
  uniformFieldRegion : Set (Time × Space 3)
  pivotPointLabel : BarPoint
  freeEndLabel : BarPoint
  isUniformBar : Bool
  pivotIsFrictionless : Bool
  pivotAxisDirection : PageNormalDirection
  gravityDirection : InPlaneDirection
  magneticFieldDirection : PageNormalDirection
  positiveCurrentDirection : BarCurrentDirection
  gravitationalTorqueSense : TorqueSense
  positiveMagneticTorqueSense : TorqueSense

/-! ## Problem data, figure evidence, and governing laws -/

/-!
Problem-statement and primary-raster readouts.  The standard-gravity
calibration makes explicit the conventional numerical constant needed to
compare with the displayed answer choices.  No current value appears here.
-/
structure MatchesProblemAndFigureReadouts
    (setup : PivotedConductingBarSetup) : Prop where
  pointAIsShown : setup.figure.pointShown .a = true
  pointBIsShown : setup.figure.pointShown .b = true
  xAxisIsShown : setup.figure.axisShown .x = true
  yAxisIsShown : setup.figure.axisShown .y = true
  barRunsFromAToB :
    setup.figure.barFirstEndpoint = .a ∧ setup.figure.barSecondEndpoint = .b
  thetaArcIsAtA : setup.figure.angleArcVertex = .a
  thetaSymbolIsShown : setup.figure.thetaLabelShown = true
  barIsAbovePositiveXAxis : setup.figure.barAbovePositiveXAxis = true
  fieldCrossesAreShown : setup.figure.uniformFieldCrossesShown = true
  fieldLabelIsShown : setup.figure.magneticFieldLabelShown = true
  massKilograms : massReadout MassUnit.kilograms setup.barMass = 12 / 1000
  lengthCentimeters :
    lengthReadout LengthUnit.centimeters setup.barLength = 30
  lengthMeters : lengthReadout LengthUnit.meters setup.barLength = 3 / 10
  magneticFieldTeslas :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude = 15 / 100
  angleRadians :
    setup.barAngleAboveHorizontalRadians = degreesToRadians 30
  standardGravity :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      98 / 10

/-- Prose-level properties and signed-orientation conventions of the setup. -/
structure MatchesPivotedUniformBarScenario
    (setup : PivotedConductingBarSetup) : Prop where
  pivotIsAtA : setup.pivotPointLabel = .a
  freeEndIsB : setup.freeEndLabel = .b
  barIsUniform : setup.isUniformBar = true
  pivotHasNoFriction : setup.pivotIsFrictionless = true
  pivotAxisPointsOutOfPage : setup.pivotAxisDirection = .outOfPage
  gravityPointsDownward : setup.gravityDirection = .negativeY
  fieldPointsIntoPage : setup.magneticFieldDirection = .intoPage
  positiveCurrentRunsFromAToB :
    setup.positiveCurrentDirection = .fromAToB
  gravityProducesClockwiseTorque :
    setup.gravitationalTorqueSense = .clockwise
  positiveCurrentProducesCounterclockwiseTorque :
    setup.positiveMagneticTorqueSense = .counterclockwise

/-- Positivity and non-vacuity conditions for the physical apparatus. -/
structure HasPhysicalBarParameters
    (setup : PivotedConductingBarSetup) : Prop where
  massPositive : 0 < massReadout MassUnit.kilograms setup.barMass
  lengthPositive : 0 < lengthReadout LengthUnit.meters setup.barLength
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  fieldRegionNonempty : setup.uniformFieldRegion.Nonempty

/-!
The scalar flux-density magnitude calibrates Physlib's spacetime-dependent
magnetic vector field throughout the region marked by uniform crosses.
-/
structure HasUniformAppliedMagneticField
    (setup : PivotedConductingBarSetup) : Prop where
  uniformMagnitude : ∀ time position,
    (time, position) ∈ setup.uniformFieldRegion →
      ‖setup.magneticField time position‖ =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude

/-!
School-level statics laws for a uniform straight bar pivoted at one endpoint.
The magnetic-torque equation is the integral of
`dτ = r × (I dℓ × B)` along the bar.  These are general relations among
independent observables; they do not state the solved current.
-/
structure SatisfiesUniformBarTorqueLaws
    (setup : PivotedConductingBarSetup) : Prop where
  centerOfMassAtMidpoint :
    lengthReadout LengthUnit.meters setup.centerOfMassDistanceFromA =
      lengthReadout LengthUnit.meters setup.barLength / 2
  weightLaw :
    forceInNewtons setup.weightMagnitude =
      massReadout MassUnit.kilograms setup.barMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  gravitationalTorqueLaw :
    torqueInNewtonMeters setup.gravitationalTorqueAboutA =
      -(lengthReadout LengthUnit.meters setup.centerOfMassDistanceFromA *
        forceInNewtons setup.weightMagnitude *
          Real.cos setup.barAngleAboveHorizontalRadians)
  distributedMagneticTorqueLaw :
    torqueInNewtonMeters setup.magneticTorqueAboutA =
      electricCurrentInAmperes setup.current *
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthReadout LengthUnit.meters setup.barLength ^ 2 / 2
  netTorqueIsSum :
    torqueInNewtonMeters setup.netTorqueAboutA =
      torqueInNewtonMeters setup.gravitationalTorqueAboutA +
        torqueInNewtonMeters setup.magneticTorqueAboutA

/-- Rotational equilibrium means zero signed net torque about the pivot `a`. -/
def IsInRotationalEquilibrium
    (setup : PivotedConductingBarSetup) : Prop :=
  torqueInNewtonMeters setup.netTorqueAboutA = 0

/-! ## Answer choices and target conclusions -/

/-- Labels of the four current choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current readout, in amperes, displayed beside each answer label. -/
def answerCurrentInAmperes : AnswerChoice → ℝ
  | .A => 4.52
  | .B => 2.26
  | .C => 15.1
  | .D => 2.60

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Agreement to the displayed hundredth of an ampere.  The half-unit in the last
printed place is `0.005 A`.
-/
def AnswerMatchesCurrentToDisplayedPrecision
    (setup : PivotedConductingBarSetup) (choice : AnswerChoice) : Prop :=
  |electricCurrentInAmperes setup.current - answerCurrentInAmperes choice| ≤
    5 / 1000

/-- A choice is strictly nearer to the required current than every rival. -/
def IsUniqueClosestCurrentChoice
    (setup : PivotedConductingBarSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |electricCurrentInAmperes setup.current - answerCurrentInAmperes choice| <
      |electricCurrentInAmperes setup.current - answerCurrentInAmperes other|

/-!
Torque balance gives the general required-current relation
`I = m g cos(theta) / (B L)`.  This is a conclusion, not a premise field.
-/
lemma requiredCurrent_formula
    (setup : PivotedConductingBarSetup)
    (_scenario : MatchesPivotedUniformBarScenario setup)
    (_physical : HasPhysicalBarParameters setup)
    (_laws : SatisfiesUniformBarTorqueLaws setup)
    (_equilibrium : IsInRotationalEquilibrium setup) :
    electricCurrentInAmperes setup.current =
      massReadout MassUnit.kilograms setup.barMass *
          accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
          Real.cos setup.barAngleAboveHorizontalRadians /
        (magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
          lengthReadout LengthUnit.meters setup.barLength) := by
  rcases _laws with ⟨hcom, hweight, hgrav, hmag, hnet⟩
  have hbalance :
      torqueInNewtonMeters setup.gravitationalTorqueAboutA +
          torqueInNewtonMeters setup.magneticTorqueAboutA = 0 := by
    rw [← hnet]
    exact _equilibrium
  rw [hgrav, hmag, hcom, hweight] at hbalance
  apply
    (eq_div_iff
      (mul_ne_zero
        (ne_of_gt _physical.fieldMagnitudePositive)
        (ne_of_gt _physical.lengthPositive))).2
  have hlengthPositive := _physical.lengthPositive
  ring_nf at hbalance ⊢
  nlinarith

/-!
For `m = 0.0120 kg`, `L = 0.300 m`, `B = 0.150 T`, `theta = 30°`,
and `g = 9.80 m/s²`, the equilibrium current is within `0.005 A` of
`2.26 A` and is closer to choice B than to every other displayed value.

This declaration formalizes `thm:physics:phyx_mini_0951:target`.  Neither the
rounded value nor answer B occurs in any hypothesis.
-/
theorem problem_phyx_mini_0951
    (setup : PivotedConductingBarSetup)
    (_data : MatchesProblemAndFigureReadouts setup)
    (_scenario : MatchesPivotedUniformBarScenario setup)
    (_physical : HasPhysicalBarParameters setup)
    (_uniformField : HasUniformAppliedMagneticField setup)
    (_laws : SatisfiesUniformBarTorqueLaws setup)
    (_equilibrium : IsInRotationalEquilibrium setup) :
    AnswerMatchesCurrentToDisplayedPrecision setup recordedDatasetAnswer ∧
      IsUniqueClosestCurrentChoice setup recordedDatasetAnswer := by
  have hI :=
    requiredCurrent_formula setup _scenario _physical _laws _equilibrium
  rw [_data.massKilograms, _data.standardGravity,
    _data.magneticFieldTeslas, _data.lengthMeters, _data.angleRadians] at hI
  have hangle : degreesToRadians 30 = Real.pi / 6 := by
    unfold degreesToRadians
    ring
  rw [hangle, Real.cos_pi_div_six] at hI
  ring_nf at hI
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := by
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hlower :
      (113 : ℝ) / 50 ≤ electricCurrentInAmperes setup.current := by
    nlinarith
  have hupper :
      electricCurrentInAmperes setup.current ≤ (453 : ℝ) / 200 := by
    nlinarith
  constructor
  · change |electricCurrentInAmperes setup.current - 2.26| ≤ 5 / 1000
    rw [abs_of_nonneg]
    · norm_num at hupper ⊢
      linarith
    · norm_num at hlower ⊢
      linarith
  · intro other hother
    fin_cases other
    · change |electricCurrentInAmperes setup.current - 2.26| <
        |electricCurrentInAmperes setup.current - 4.52|
      rw [abs_of_nonneg, abs_of_nonpos]
      · norm_num at hlower hupper ⊢
        linarith
      · norm_num at hupper ⊢
        linarith
      · norm_num at hlower ⊢
        linarith
    · exact (hother rfl).elim
    · change |electricCurrentInAmperes setup.current - 2.26| <
        |electricCurrentInAmperes setup.current - 15.1|
      rw [abs_of_nonneg, abs_of_nonpos]
      · norm_num at hlower hupper ⊢
        linarith
      · norm_num at hupper ⊢
        linarith
      · norm_num at hlower ⊢
        linarith
    · change |electricCurrentInAmperes setup.current - 2.26| <
        |electricCurrentInAmperes setup.current - 2.60|
      rw [abs_of_nonneg, abs_of_nonpos]
      · norm_num at hlower hupper ⊢
        linarith
      · norm_num at hupper ⊢
        linarith
      · norm_num at hlower ⊢
        linarith

end PhyXMiniProblems.ProblemPhyXMini0951
