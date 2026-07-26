import Mathlib
import Physlib.ClassicalMechanics.RigidBody.AngularMomentum
import Physlib.ClassicalMechanics.RigidBody.SolidSphere
import Physlib.SpaceAndTime.Space.CrossProduct
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0627

open Dimension MeasureTheory
open scoped Matrix

/-!
# The g-factor of a uniformly charged, uniformly massive rotating sphere

The source first calls the object a spherical shell, but then supplies the
volume-density formula `rho = Q / ((4/3) * pi * R^3)` and the solid-sphere
inertia coefficient `c = 2/5`.  The declarations below retain the shell wording
as source metadata while making the volume-distributed solid-ball model used
by the question explicit.

All physical quantities are unit-independent `Dimensionful` values tagged by
Physlib dimensions.  Real numbers occur only as coherent-SI readouts,
dimensionless angles and coefficients, raster data, or displayed answer
values.

Assumption/target split:

* `MatchesSpinningSphereScenario` records the shell wording, central point,
  z-axis, and rigid rotation;
* `MatchesStatedUniformDistributionData` records the stated uniform-volume
  charge density and `c = 2/5`, and identifies the mass distribution with
  Physlib's `RigidBody.solidSphere`;
* `MatchesSuppliedRotatingSphereFigure` records the primary image's labels and
  spherical-band geometry;
* `SatisfiesRigidRotationAndDipoleLaws` states rigid charge transport, the
  current-density definition of magnetic dipole moment, and Physlib's rigid-
  body angular momentum;
* `SatisfiesGFactorRelation` states the source's defining proportionality for
  an otherwise independent dimensionless `gFactor`; and
* `gFactor = 1` and answer A occur only in the final theorem conclusion.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev ChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- The inverse-time dimension of angular velocity; radians are dimensionless. -/
def angularVelocityDimension : Dimension := T𝓭⁻¹

/-- The dimension `M L^2 T^-1` of angular momentum. -/
def angularMomentumDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- The dimension `C L^2 T^-1` of magnetic dipole moment. -/
def magneticMomentDimension : Dimension :=
  C𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- The dimension `C L^-3` of volume charge density. -/
def volumeChargeDensityDimension : Dimension :=
  C𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The dimension `C L^-2` of the surface-density symbol printed in the image. -/
def surfaceChargeDensityDimension : Dimension :=
  C𝓭 * L𝓭⁻¹ * L𝓭⁻¹

/-- The dimension `C T^-1 L^-2` of electric current density. -/
def currentDensityDimension : Dimension :=
  C𝓭 * T𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- A three-component angular-velocity vector. -/
abbrev AngularVelocityVector : Type :=
  Dimensionful (WithDim angularVelocityDimension (Fin 3 → ℝ))

/-- A three-component angular-momentum vector. -/
abbrev AngularMomentumVector : Type :=
  Dimensionful (WithDim angularMomentumDimension (Fin 3 → ℝ))

/-- A three-component magnetic-dipole-moment vector. -/
abbrev MagneticMomentVector : Type :=
  Dimensionful (WithDim magneticMomentDimension (Fin 3 → ℝ))

/-- A signed uniform volume charge density. -/
abbrev VolumeChargeDensityQuantity : Type :=
  Dimensionful (WithDim volumeChargeDensityDimension ℝ)

/-- The `sigma` density label from the primary image, interpreted as surface density. -/
abbrev SurfaceChargeDensityQuantity : Type :=
  Dimensionful (WithDim surfaceChargeDensityDimension ℝ)

/-- A three-component electric current-density field value. -/
abbrev CurrentDensityVector : Type :=
  Dimensionful (WithDim currentDensityDimension (Fin 3 → ℝ))

/-- Nonnegative mass readout in coherent SI units (kilograms). -/
def massMagnitudeInKilograms (mass : MassQuantity) : NNReal :=
  (mass UnitChoices.SI).val

/-- Mass readout in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massMagnitudeInKilograms mass

/-- Nonnegative length readout in coherent SI units (metres). -/
def lengthMagnitudeInMeters (length : LengthQuantity) : NNReal :=
  (length UnitChoices.SI).val

/-- Length readout in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthMagnitudeInMeters length

/-- Charge readout in coulombs. -/
def chargeInCoulombs (charge : ChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Angular-velocity readout in radians per second. -/
def angularVelocityInRadiansPerSecond
    (angularVelocity : AngularVelocityVector) : Fin 3 → ℝ :=
  (angularVelocity UnitChoices.SI).val

/-- Angular-momentum readout in kilogram-square-metres per second. -/
def angularMomentumInSI
    (angularMomentum : AngularMomentumVector) : Fin 3 → ℝ :=
  (angularMomentum UnitChoices.SI).val

/-- Magnetic-moment readout in coulomb-square-metres per second. -/
def magneticMomentInSI
    (magneticMoment : MagneticMomentVector) : Fin 3 → ℝ :=
  (magneticMoment UnitChoices.SI).val

/-- Volume charge-density readout in coulombs per cubic metre. -/
def volumeChargeDensityInSI
    (chargeDensity : VolumeChargeDensityQuantity) : ℝ :=
  (chargeDensity UnitChoices.SI).val

/-- Surface charge-density readout in coulombs per square metre. -/
def surfaceChargeDensityInSI
    (chargeDensity : SurfaceChargeDensityQuantity) : ℝ :=
  (chargeDensity UnitChoices.SI).val

/-- Current-density readout in amperes per square metre. -/
def currentDensityInSI
    (currentDensity : CurrentDensityVector) : Fin 3 → ℝ :=
  (currentDensity UnitChoices.SI).val

/-! ## Physical roles and primary-figure labels -/

/-- The literal object description used in the prose. -/
inductive SourceShapeDescription where
  | sphericalShell
  deriving DecidableEq, Repr

/-- The distribution model selected by the supplied `rho` and `c` formulas. -/
inductive EffectiveDistributionModel where
  | uniformSolidBall
  deriving DecidableEq, Repr

/-- Literal labels visible in image `627.png`. -/
inductive FigureLabel where
  | zAxis
  | centerO
  | radiusR
  | polarAngleTheta
  | meridionalArcRdTheta
  | ringLineElementDl
  | angularVelocityOmega
  | totalChargeQ
  | totalMassM
  | chargeDensitySigma
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative and geometric data visible in the `578 x 630` primary raster.
Angles and pixel counts are dimensionless.  The two labelled arc elements
retain physical length dimensions.
-/
structure RotatingSphereFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  labelShown : FigureLabel → Bool
  transparentSphereShown : Bool
  verticalAxisShown : Bool
  circularBandShown : Bool
  rotationArrowShown : Bool
  bandDirectionArrowShown : Bool
  polarAngleRadians : ℝ
  polarIncrementRadians : ℝ
  ringRadius : LengthQuantity
  meridionalArcElement : LengthQuantity
  ringLineElement : LengthQuantity

/-!
Independent physical quantities of the rotating object.  The `gFactor`,
magnetic moment, and angular momentum are stored independently; none is
defined from answer A.
-/
structure SpinningSphereSetup where
  sourceShapeDescription : SourceShapeDescription
  effectiveDistributionModel : EffectiveDistributionModel
  spatialCoordinatesUseSI : Bool
  center : Space 3
  rotationAxis : Fin 3 → ℝ
  totalCharge : ChargeQuantity
  totalMass : MassQuantity
  radius : LengthQuantity
  volumeChargeDensityRho : VolumeChargeDensityQuantity
  figureSurfaceDensitySigma : SurfaceChargeDensityQuantity
  angularVelocity : AngularVelocityVector
  angularMomentum : AngularMomentumVector
  magneticMoment : MagneticMomentVector
  currentDensity : Space 3 → CurrentDensityVector
  massBody : RigidBody 3
  momentOfInertiaCoefficient : ℝ
  gFactor : ℝ
  figure : RotatingSphereFigure

/-- Coordinate displacement from the sphere's center in the chosen SI spatial chart. -/
def displacementFromCenter
    (setup : SpinningSphereSetup) (point : Space 3) : Fin 3 → ℝ :=
  fun i => point.val i - setup.center.val i

/-- The closed spatial region occupied by the uniform solid-ball model. -/
def occupiedBall (setup : SpinningSphereSetup) : Set (Space 3) :=
  Metric.closedBall setup.center (lengthInMeters setup.radius)

/-- SI current-density field associated with the setup. -/
def setupCurrentDensityInSI
    (setup : SpinningSphereSetup) (point : Space 3) : Fin 3 → ℝ :=
  currentDensityInSI (setup.currentDensity point)

/-- Integrand in `mu = (1/2) integral (r cross J) dV`. -/
def magneticMomentIntegrandInSI
    (setup : SpinningSphereSetup) (point : Space 3) : Fin 3 → ℝ :=
  (1 / 2 : ℝ) •
    (displacementFromCenter setup point ⨯₃ setupCurrentDensityInSI setup point)

/-! ## Scenario, supplied data, figure evidence, and governing physics -/

/--
The qualitative source scenario: a charged spherical object rotates about the
z-axis through its center.  The shell wording is retained here independently
of the later effective uniform-volume model.
-/
structure MatchesSpinningSphereScenario
    (setup : SpinningSphereSetup) : Prop where
  sourceCallsObjectShell :
    setup.sourceShapeDescription = .sphericalShell
  spatialCoordinatesCalibratedInSI : setup.spatialCoordinatesUseSI = true
  centerAtCoordinateOrigin : setup.center = 0
  rotationAxisXComponent : setup.rotationAxis 0 = 0
  rotationAxisYComponent : setup.rotationAxis 1 = 0
  rotationAxisZComponent : setup.rotationAxis 2 = 1
  angularVelocityHasNoXComponent :
    angularVelocityInRadiansPerSecond setup.angularVelocity 0 = 0
  angularVelocityHasNoYComponent :
    angularVelocityInRadiansPerSecond setup.angularVelocity 1 = 0

/-!
The two distribution formulas supplied by the question.  The equality with
`RigidBody.solidSphere` uses Physlib's uniform mass-distribution model.  No
magnetic moment, angular momentum, `gFactor`, or answer choice occurs here.
-/
structure MatchesStatedUniformDistributionData
    (setup : SpinningSphereSetup) : Prop where
  effectiveModelIsUniformSolidBall :
    setup.effectiveDistributionModel = .uniformSolidBall
  massDistributionIsPhyslibSolidSphere :
    setup.massBody =
      RigidBody.solidSphere 3
        (massMagnitudeInKilograms setup.totalMass)
        (lengthMagnitudeInMeters setup.radius)
  uniformVolumeChargeDensity :
    volumeChargeDensityInSI setup.volumeChargeDensityRho =
      chargeInCoulombs setup.totalCharge /
        ((4 / 3 : ℝ) * Real.pi * lengthInMeters setup.radius ^ 3)
  uniformMassInertiaCoefficient :
    setup.momentOfInertiaCoefficient = (2 : ℝ) / 5

/-!
Direct evidence from image `627.png`: the transparent sphere, vertical z-axis,
point O, radius R, angle theta, `R dtheta`, ring element `dl`, rotation omega,
and the `Q, M, sigma` parameter block.  The geometric equations interpret only
the printed `R dtheta` and latitude-band construction; they state no g-factor.
-/
structure MatchesSuppliedRotatingSphereFigure
    (setup : SpinningSphereSetup) : Prop where
  rasterWidth : setup.figure.rasterWidthPixels = 578
  rasterHeight : setup.figure.rasterHeightPixels = 630
  everyPrintedLabelIsShown : ∀ label, setup.figure.labelShown label = true
  transparentSphereVisible : setup.figure.transparentSphereShown = true
  verticalAxisVisible : setup.figure.verticalAxisShown = true
  circularBandVisible : setup.figure.circularBandShown = true
  angularVelocityArrowVisible : setup.figure.rotationArrowShown = true
  bandArrowVisible : setup.figure.bandDirectionArrowShown = true
  latitudeRingRadius :
    lengthInMeters setup.figure.ringRadius =
      lengthInMeters setup.radius * Real.sin setup.figure.polarAngleRadians
  printedMeridionalArcRelation :
    lengthInMeters setup.figure.meridionalArcElement =
      lengthInMeters setup.radius * setup.figure.polarIncrementRadians

/-- Positivity and nondegeneracy assumptions needed to determine a unique g-factor. -/
structure HasPhysicalSpinningSphereParameters
    (setup : SpinningSphereSetup) : Prop where
  positiveMass : 0 < massInKilograms setup.totalMass
  positiveRadius : 0 < lengthInMeters setup.radius
  nonzeroCharge : chargeInCoulombs setup.totalCharge ≠ 0
  nonzeroRotationAboutZ :
    angularVelocityInRadiansPerSecond setup.angularVelocity 2 ≠ 0
  polarAngleRange :
    0 ≤ setup.figure.polarAngleRadians ∧
      setup.figure.polarAngleRadians ≤ Real.pi
  positivePolarIncrement : 0 < setup.figure.polarIncrementRadians
  positiveRingLineElement :
    0 < lengthInMeters setup.figure.ringLineElement

/-!
General governing laws for a rigidly rotating charged body:

* inside the occupied ball, `J = rho * (omega cross r)`;
* outside it, the current density vanishes;
* `mu = (1/2) integral (r cross J) dV`; and
* mass angular momentum is Physlib's `RigidBody.angularMomentum`.

These laws contain neither the special solid-sphere coefficients `1/5` and
`2/5` nor the current target `g = 1`.
-/
structure SatisfiesRigidRotationAndDipoleLaws
    (setup : SpinningSphereSetup) : Prop where
  rigidChargeCurrentInside : ∀ point ∈ occupiedBall setup,
    setupCurrentDensityInSI setup point =
      volumeChargeDensityInSI setup.volumeChargeDensityRho •
        (angularVelocityInRadiansPerSecond setup.angularVelocity ⨯₃
          displacementFromCenter setup point)
  noChargeCurrentOutside : ∀ point ∉ occupiedBall setup,
    setupCurrentDensityInSI setup point = 0
  magneticDipoleMomentFromCurrent :
    magneticMomentInSI setup.magneticMoment =
      ∫ point in occupiedBall setup,
        magneticMomentIntegrandInSI setup point ∂volume
  rigidBodyAngularMomentum :
    angularMomentumInSI setup.angularMomentum =
      setup.massBody.angularMomentum
        (angularVelocityInRadiansPerSecond setup.angularVelocity)

/-!
The defining relation from the problem statement,
`mu = g * (Q/(2M)) * L`.  This constrains an independent `gFactor` but does
not assume its requested value.
-/
structure SatisfiesGFactorRelation
    (setup : SpinningSphereSetup) : Prop where
  gyromagneticProportionality :
    magneticMomentInSI setup.magneticMoment =
      (setup.gFactor * chargeInCoulombs setup.totalCharge /
          (2 * massInKilograms setup.totalMass)) •
        angularMomentumInSI setup.angularMomentum

/-! ## Derived solid-sphere relations -/

/-!
Physlib's solid-sphere inertia tensor and angular-momentum law yield
`L = (2/5) M R^2 omega` in coherent SI readouts.  This is an intermediate
mechanical result and contains no charge, magnetic moment, or g-factor.
-/
lemma uniformMassSphereAngularMomentumReadout
    (setup : SpinningSphereSetup)
    (_scenario : MatchesSpinningSphereScenario setup)
    (_data : MatchesStatedUniformDistributionData setup)
    (_physical : HasPhysicalSpinningSphereParameters setup)
    (_laws : SatisfiesRigidRotationAndDipoleLaws setup) :
    angularMomentumInSI setup.angularMomentum =
      ((2 / 5 : ℝ) * massInKilograms setup.totalMass *
          lengthInMeters setup.radius ^ 2) •
        angularVelocityInRadiansPerSecond setup.angularVelocity := by
  sorry

/-!
Integrating `mu = (1/2) integral (r cross J) dV` for the stated uniform
volume charge density gives `mu = (1/5) Q R^2 omega`.  It is kept as a derived
lemma rather than inserted into a premise.
-/
lemma uniformChargeSphereMagneticMomentReadout
    (setup : SpinningSphereSetup)
    (_scenario : MatchesSpinningSphereScenario setup)
    (_data : MatchesStatedUniformDistributionData setup)
    (_physical : HasPhysicalSpinningSphereParameters setup)
    (_laws : SatisfiesRigidRotationAndDipoleLaws setup) :
    magneticMomentInSI setup.magneticMoment =
      ((1 / 5 : ℝ) * chargeInCoulombs setup.totalCharge *
          lengthInMeters setup.radius ^ 2) •
        angularVelocityInRadiansPerSecond setup.angularVelocity := by
  sorry

/-! ## Displayed answers and current target -/

/-- Labels of the four g-factor choices in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless g-factor printed beside each answer label. -/
def displayedGFactor : AnswerChoice → ℝ
  | .A => 1
  | .B => 0
  | .C => 3
  | .D => 2

/-- Dataset metadata recording answer A; this is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- Exact agreement of the inferred dimensionless g-factor with a displayed choice. -/
def MatchesDisplayedGFactor
    (setup : SpinningSphereSetup) (choice : AnswerChoice) : Prop :=
  setup.gFactor = displayedGFactor choice

/-!
For the supplied uniform volume charge and mass distributions,
`mu = (1/5) Q R^2 omega` and `L = (2/5) M R^2 omega`.  Comparison with
`mu = g (Q/(2M)) L`, under the nondegeneracy assumptions, gives `g = 1`,
which is answer A.

Blueprint: `thm:physics:phyx_mini_0627:target`.
-/
theorem uniformlyChargedMassiveSphereGFactor
    (setup : SpinningSphereSetup)
    (_scenario : MatchesSpinningSphereScenario setup)
    (_data : MatchesStatedUniformDistributionData setup)
    (_figure : MatchesSuppliedRotatingSphereFigure setup)
    (_physical : HasPhysicalSpinningSphereParameters setup)
    (_laws : SatisfiesRigidRotationAndDipoleLaws setup)
    (_gRelation : SatisfiesGFactorRelation setup) :
    setup.gFactor = 1 ∧ MatchesDisplayedGFactor setup .A := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0627
