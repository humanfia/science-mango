import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0958

open Dimension

/-!
# Speed at the top of a cycloidal trajectory in crossed fields

A positively charged particle starts from rest at the origin.  A uniform
electric field points along the positive `y`-axis, while a uniform magnetic
field points out of the page (the positive `z`-axis).  The primary raster
shows the resulting dashed cycloidal path and its rightward tangent at an
uppermost point.

Physical magnitudes are represented by unit-independent Physlib
`Dimensionful` quantities.  Real numbers appear only at coherent-SI readout
boundaries and in the final scalar relation between those readouts.

Assumption/target split:

* governing laws: the work-energy relation from the origin to the top,
  centripetal acceleration, the Lorentz-force magnitude at the top, and
  Newton's second law;
* previous-part results: none;
* figure/data readouts: positive charge at the origin, the `x`/`y` axes,
  upward electric-field arrow, out-of-page magnetic-field dots, dashed
  cycloidal path, rightward top tangent, and the given curvature radius
  `R = 2y`;
* current target conclusion: the speed at the top is `2E / B`.

The top speed, the field magnitudes, the radius, the height, the acceleration,
and the net force are independent fields of the setup.  No premise below
states the requested speed formula.
-/

/-! ## Dimensions and physical quantities -/

/-- Velocity and speed have physical dimension `L T⁻¹`. -/
def velocityDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- Acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Force has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric-field strength has physical dimension `M L T⁻² C⁻¹`. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density has physical dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent positive-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent length magnitude. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A unit-independent position vector in the three-dimensional scene. -/
abbrev SpatialPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 (EuclideanSpace ℝ (Fin 3)))

/-- A unit-independent velocity vector in the three-dimensional scene. -/
abbrev SpatialVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 3)))

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim velocityDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A unit-independent electric-field vector. -/
abbrev SpatialElectricFieldQuantity : Type :=
  Dimensionful
    (WithDim electricFieldStrengthDimension (EuclideanSpace ℝ (Fin 3)))

/-- A nonnegative, unit-independent electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A unit-independent magnetic-flux-density vector. -/
abbrev SpatialMagneticFieldQuantity : Type :=
  Dimensionful
    (WithDim magneticFluxDensityDimension (EuclideanSpace ℝ (Fin 3)))

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityQuantity : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-! ## Coherent-SI readouts -/

/-- Coordinate `0`, horizontal and positive to the right in the raster. -/
def xAxis : Fin 3 := 0

/-- Coordinate `1`, vertical and positive upward in the raster. -/
def yAxis : Fin 3 := 1

/-- Coordinate `2`, positive out of the page. -/
def zAxis : Fin 3 := 2

/-- Read a mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a positive-charge magnitude in coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a position vector in metres. -/
def positionVectorInMeters
    (position : SpatialPositionQuantity) : EuclideanSpace ℝ (Fin 3) :=
  (position UnitChoices.SI).val

/-- Read a velocity vector in metres per second. -/
def velocityVectorInMetersPerSecond
    (velocity : SpatialVelocityQuantity) : EuclideanSpace ℝ (Fin 3) :=
  (velocity UnitChoices.SI).val

/-- Read a speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a force magnitude in newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Read an electric-field vector in newtons per coulomb. -/
def electricFieldVectorInNewtonsPerCoulomb
    (field : SpatialElectricFieldQuantity) : EuclideanSpace ℝ (Fin 3) :=
  (field UnitChoices.SI).val

/-- Read an electric-field strength in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (field : ElectricFieldStrengthQuantity) : ℝ :=
  ((field UnitChoices.SI).val : ℝ)

/-- Read a magnetic-flux-density vector in teslas. -/
def magneticFieldVectorInTeslas
    (field : SpatialMagneticFieldQuantity) : EuclideanSpace ℝ (Fin 3) :=
  (field UnitChoices.SI).val

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityQuantity) : ℝ :=
  ((field UnitChoices.SI).val : ℝ)

/-! ## Scenario states and primary-raster vocabulary -/

/-- The two particle states used by the problem. -/
inductive MotionState where
  | initial
  | top
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions explicitly visible or implied by the raster. -/
inductive SpatialDirection where
  | positiveX
  | positiveY
  | outOfPage
  deriving DecidableEq, Repr

/-- The sign printed inside the particle marker. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Objects whose presence is physically relevant in image `958.png`. -/
inductive FigureObject where
  | xAxis
  | yAxis
  | positiveParticle
  | electricFieldArrow
  | magneticFieldDotGrid
  | dashedCycloidalPath
  | pathDirectionArrows
  deriving DecidableEq, Fintype, Repr

/-- Literal labels visible in image `958.png`. -/
inductive FigureLabel where
  | x
  | y
  | electricFieldE
  | magneticFieldB
  deriving DecidableEq, Fintype, Repr

/-- Primary-raster data, kept separate from the physical quantities. -/
structure CrossedFieldsFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  particleChargeSign : ChargeSign
  electricFieldArrowDirection : SpatialDirection
  magneticFieldMarkerDirection : SpatialDirection
  topTangentDirection : SpatialDirection
  particleDrawnAtAxesOrigin : Bool
  trajectoryLeavesOrigin : Bool

/-!
Independent physical data for the particle, uniform fields, and selected top
point.  The field maps retain their spatial physical role even though their
uniformity will make their values independent of position.
-/
structure CrossedFieldsParticleSetup where
  figure : CrossedFieldsFigure
  particleMass : MassQuantity
  particleChargeMagnitude : ChargeMagnitudeQuantity
  electricField : SpatialPositionQuantity → SpatialElectricFieldQuantity
  magneticField : SpatialPositionQuantity → SpatialMagneticFieldQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  magneticFluxDensity : MagneticFluxDensityQuantity
  position : MotionState → SpatialPositionQuantity
  velocity : MotionState → SpatialVelocityQuantity
  topHeight : LengthQuantity
  topSpeed : SpeedQuantity
  topRadiusOfCurvature : LengthQuantity
  topCentripetalAcceleration : AccelerationMagnitudeQuantity
  topNetDownwardForce : ForceMagnitudeQuantity

/-! ## Figure evidence, scenario assumptions, geometry, and laws -/

/-- Literal and qualitative facts read from the primary image. -/
structure MatchesPrimaryCrossedFieldsFigure
    (setup : CrossedFieldsParticleSetup) : Prop where
  xAxisShown : setup.figure.showsObject .xAxis = true
  yAxisShown : setup.figure.showsObject .yAxis = true
  positiveParticleShown : setup.figure.showsObject .positiveParticle = true
  electricFieldArrowShown :
    setup.figure.showsObject .electricFieldArrow = true
  magneticFieldDotsShown :
    setup.figure.showsObject .magneticFieldDotGrid = true
  dashedCycloidalPathShown :
    setup.figure.showsObject .dashedCycloidalPath = true
  pathDirectionArrowsShown :
    setup.figure.showsObject .pathDirectionArrows = true
  xLabelShown : setup.figure.showsLabel .x = true
  yLabelShown : setup.figure.showsLabel .y = true
  electricFieldLabelShown :
    setup.figure.showsLabel .electricFieldE = true
  magneticFieldLabelShown :
    setup.figure.showsLabel .magneticFieldB = true
  particleMarkedPositive : setup.figure.particleChargeSign = .positive
  particleAtOrigin : setup.figure.particleDrawnAtAxesOrigin = true
  pathStartsAtOrigin : setup.figure.trajectoryLeavesOrigin = true
  electricFieldArrowUpward :
    setup.figure.electricFieldArrowDirection = .positiveY
  magneticFieldDotsPointOutOfPage :
    setup.figure.magneticFieldMarkerDirection = .outOfPage
  topTangentPointsRight : setup.figure.topTangentDirection = .positiveX

/-!
The prose model: static spatially uniform crossed fields, a positive particle,
and rest at the coordinate origin.  Component equalities tie the vector fields
to the independent nonnegative field-strength quantities.
-/
structure MatchesCrossedFieldsScenario
    (setup : CrossedFieldsParticleSetup) : Prop where
  electricFieldUniform : ∀ position,
    setup.electricField position =
      setup.electricField (setup.position .initial)
  magneticFieldUniform : ∀ position,
    setup.magneticField position =
      setup.magneticField (setup.position .initial)
  electricFieldXComponent : ∀ position,
    electricFieldVectorInNewtonsPerCoulomb (setup.electricField position) xAxis = 0
  electricFieldYComponent : ∀ position,
    electricFieldVectorInNewtonsPerCoulomb (setup.electricField position) yAxis =
      electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  electricFieldZComponent : ∀ position,
    electricFieldVectorInNewtonsPerCoulomb (setup.electricField position) zAxis = 0
  magneticFieldXComponent : ∀ position,
    magneticFieldVectorInTeslas (setup.magneticField position) xAxis = 0
  magneticFieldYComponent : ∀ position,
    magneticFieldVectorInTeslas (setup.magneticField position) yAxis = 0
  magneticFieldZComponent : ∀ position,
    magneticFieldVectorInTeslas (setup.magneticField position) zAxis =
      magneticFluxDensityInTeslas setup.magneticFluxDensity
  startsAtOrigin :
    positionVectorInMeters (setup.position .initial) = 0
  startsFromRest :
    velocityVectorInMetersPerSecond (setup.velocity .initial) = 0

/-- Positivity assumptions for the nondegenerate physical situation. -/
structure NondegenerateCrossedFieldsData
    (setup : CrossedFieldsParticleSetup) : Prop where
  massPositive : massInKilograms setup.particleMass > 0
  chargePositive :
    chargeMagnitudeInCoulombs setup.particleChargeMagnitude > 0
  electricFieldPositive :
    electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength > 0
  magneticFieldPositive :
    magneticFluxDensityInTeslas setup.magneticFluxDensity > 0
  topHeightPositive : lengthInMeters setup.topHeight > 0
  topSpeedPositive : speedInMetersPerSecond setup.topSpeed > 0
  topRadiusPositive : lengthInMeters setup.topRadiusOfCurvature > 0

/-!
The given cycloid geometry and top-point kinematics.  In particular, the
radius equality is an allowed supplied result, not the requested speed.
-/
structure GivenCycloidTopGeometry
    (setup : CrossedFieldsParticleSetup) : Prop where
  topHeightIsYCoordinate :
    positionVectorInMeters (setup.position .top) yAxis =
      lengthInMeters setup.topHeight
  topLiesInPage :
    positionVectorInMeters (setup.position .top) zAxis = 0
  topVelocityXComponent :
    velocityVectorInMetersPerSecond (setup.velocity .top) xAxis =
      speedInMetersPerSecond setup.topSpeed
  topVelocityYComponent :
    velocityVectorInMetersPerSecond (setup.velocity .top) yAxis = 0
  topVelocityZComponent :
    velocityVectorInMetersPerSecond (setup.velocity .top) zAxis = 0
  radiusOfCurvatureTwiceHeight :
    lengthInMeters setup.topRadiusOfCurvature =
      2 * lengthInMeters setup.topHeight

/-!
Governing scalar-magnitude laws at the selected top point.  The work-energy
equation uses the initial rest state and the fact that a magnetic force does
no work.  The Lorentz equation records that, at a rightward top tangent with
`B` out of the page, the magnetic contribution is downward and the electric
contribution is upward.  Newton's equation then relates the independent net
force and acceleration quantities.
-/
structure SatisfiesTopPointDynamics
    (setup : CrossedFieldsParticleSetup) : Prop where
  workEnergyFromRest :
    (1 / 2 : ℝ) * massInKilograms setup.particleMass *
        speedInMetersPerSecond setup.topSpeed ^ 2 =
      chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
        electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength *
        lengthInMeters setup.topHeight
  centripetalAcceleration :
    accelerationMagnitudeInMetersPerSecondSquared
        setup.topCentripetalAcceleration =
      speedInMetersPerSecond setup.topSpeed ^ 2 /
        lengthInMeters setup.topRadiusOfCurvature
  topLorentzForce :
    forceMagnitudeInNewtons setup.topNetDownwardForce =
      chargeMagnitudeInCoulombs setup.particleChargeMagnitude *
        (magneticFluxDensityInTeslas setup.magneticFluxDensity *
            speedInMetersPerSecond setup.topSpeed -
          electricFieldStrengthInNewtonsPerCoulomb
            setup.electricFieldStrength)
  newtonSecondLaw :
    forceMagnitudeInNewtons setup.topNetDownwardForce =
      massInKilograms setup.particleMass *
        accelerationMagnitudeInMetersPerSecondSquared
          setup.topCentripetalAcceleration

/-!
At the uppermost point of the cycloid, the particle's speed is twice the
electric-field strength divided by the magnetic flux density.

Blueprint: `thm:physics:phyx_mini_0958:target`.
-/
theorem speed_at_cycloid_top
    (setup : CrossedFieldsParticleSetup)
    (_hFigure : MatchesPrimaryCrossedFieldsFigure setup)
    (_hScenario : MatchesCrossedFieldsScenario setup)
    (_hNondegenerate : NondegenerateCrossedFieldsData setup)
    (_hGeometry : GivenCycloidTopGeometry setup)
    (_hDynamics : SatisfiesTopPointDynamics setup) :
    speedInMetersPerSecond setup.topSpeed =
      2 * electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength /
        magneticFluxDensityInTeslas setup.magneticFluxDensity := by
  let m : ℝ := massInKilograms setup.particleMass
  let q : ℝ := chargeMagnitudeInCoulombs setup.particleChargeMagnitude
  let e : ℝ :=
    electricFieldStrengthInNewtonsPerCoulomb setup.electricFieldStrength
  let b : ℝ :=
    magneticFluxDensityInTeslas setup.magneticFluxDensity
  let h : ℝ := lengthInMeters setup.topHeight
  let v : ℝ := speedInMetersPerSecond setup.topSpeed
  let r : ℝ := lengthInMeters setup.topRadiusOfCurvature
  let a : ℝ :=
    accelerationMagnitudeInMetersPerSecondSquared
      setup.topCentripetalAcceleration
  let f : ℝ := forceMagnitudeInNewtons setup.topNetDownwardForce
  have hq : q > 0 := by
    simpa only [q] using _hNondegenerate.chargePositive
  have hb : b > 0 := by
    simpa only [b] using _hNondegenerate.magneticFieldPositive
  have hh : h > 0 := by
    simpa only [h] using _hNondegenerate.topHeightPositive
  have hR : r = 2 * h := by
    simpa only [r, h] using
      _hGeometry.radiusOfCurvatureTwiceHeight
  have hWE : (1 / 2 : ℝ) * m * v ^ 2 = q * e * h := by
    simpa only [m, q, e, h, v] using
      _hDynamics.workEnergyFromRest
  have hA : a = v ^ 2 / r := by
    simpa only [a, v, r] using
      _hDynamics.centripetalAcceleration
  have hL : f = q * (b * v - e) := by
    simpa only [f, q, b, v, e] using
      _hDynamics.topLorentzForce
  have hN : f = m * a := by
    simpa only [f, m, a] using
      _hDynamics.newtonSecondLaw
  change v = 2 * e / b
  have hTwoHeight : (2 * h : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hh)
  rw [hR] at hA
  have hAcceleration : a * (2 * h) = v ^ 2 :=
    (eq_div_iff hTwoHeight).mp hA
  have hWorkEnergy : m * v ^ 2 = (q * e) * (2 * h) := by
    nlinarith [hWE]
  have hMassAccelerationTimesHeight :
      (m * a) * (2 * h) = (q * e) * (2 * h) := by
    calc
      (m * a) * (2 * h) = m * (a * (2 * h)) := by ring
      _ = m * v ^ 2 := by rw [hAcceleration]
      _ = (q * e) * (2 * h) := hWorkEnergy
  have hMassAcceleration : m * a = q * e :=
    mul_right_cancel₀ hTwoHeight hMassAccelerationTimesHeight
  have hForceBalance : q * (b * v - e) = q * e := by
    calc
      q * (b * v - e) = f := hL.symm
      _ = m * a := hN
      _ = q * e := hMassAcceleration
  have hFields : b * v - e = e :=
    mul_left_cancel₀ (ne_of_gt hq) hForceBalance
  apply (eq_div_iff (ne_of_gt hb)).2
  nlinarith [hFields]

end PhyXMiniProblems.ProblemPhyXMini0958
