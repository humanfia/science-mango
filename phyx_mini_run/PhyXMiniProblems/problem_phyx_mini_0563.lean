import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0563

open Dimension

/-!
# Gyromagnetic factor of a solid sphere with an equatorial charge ring

A rigid solid sphere of total mass `M` and radius `R` rotates about an axis
through its center.  The mass fills the sphere, while all of the nonzero total
charge `Q` lies on a thin ring on the surface in the equatorial plane.  Thus
the mass and charge do not have a common local charge-to-mass ratio.

The scalar angular momentum is the magnitude along the rotation axis, and the
magnetic moment is its signed axial component.  All basic physical quantities
are unit-independent Physlib `Dimensionful` values.  Real numbers occur only
as coherent unit readouts and as the dimensionless gyromagnetic factor and
answer choices.

Assumption/target split:

* governing laws: `I = (2/5) M R^2`, `L = I ω`, the rotating-ring law
  `μ = Q ω R^2 / 2`, and the stated relation `μ = g (Q/(2M)) L`;
* previous-part results: none;
* figure/data readouts: a solid sphere, a surface ring in its equatorial
  plane, a central perpendicular rotation axis, and the visible rotation
  arrow and dashed rear arc;
* current target: `g = 5/2`, equivalently unique selection of choice D.

In particular, the value `5/2` is not a field of any law or scenario
predicate and is not used to define the gyromagnetic factor.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- Angular speed has inverse-time dimension; radians are dimensionless. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- Moment of inertia has dimension `mass * length^2`. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- Angular momentum has dimension `mass * length^2 / time`. -/
def angularMomentumDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- Magnetic dipole moment has dimension `charge * length^2 / time`. -/
def magneticMomentDimension : Dimension :=
  C𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev ChargeQuantity : Type := Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative moment of inertia about the displayed axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative angular-momentum magnitude along the displayed axis. -/
abbrev AngularMomentumMagnitudeQuantity : Type :=
  Dimensionful (WithDim angularMomentumDimension NNReal)

/-- The signed component of magnetic moment along the displayed axis. -/
abbrev MagneticMomentAxialQuantity : Type :=
  Dimensionful (WithDim magneticMomentDimension ℝ)

/-- Read mass in the mass unit selected by a coherent system of units. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  ((mass units).val : ℝ)

/-- Read length in the length unit selected by a coherent system of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Read signed charge in the charge unit selected by the unit system. -/
def chargeReadout (units : UnitChoices) (charge : ChargeQuantity) : ℝ :=
  (charge units).val

/-- Read angular speed in radians per selected time unit. -/
def angularSpeedReadout
    (units : UnitChoices) (angularSpeed : AngularSpeedMagnitudeQuantity) : ℝ :=
  ((angularSpeed units).val : ℝ)

/-- Read moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (units : UnitChoices) (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia units).val : ℝ)

/-- Read angular momentum in coherent selected mass, length, and time units. -/
def angularMomentumReadout
    (units : UnitChoices) (angularMomentum : AngularMomentumMagnitudeQuantity) : ℝ :=
  ((angularMomentum units).val : ℝ)

/-- Read the signed axial magnetic moment in coherent selected units. -/
def magneticMomentReadout
    (units : UnitChoices) (magneticMoment : MagneticMomentAxialQuantity) : ℝ :=
  (magneticMoment units).val

/-- SI kilogram readout of the sphere's mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout UnitChoices.SI mass

/-- SI meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- SI coulomb readout of the ring's total charge. -/
def chargeInCoulombs (charge : ChargeQuantity) : ℝ :=
  chargeReadout UnitChoices.SI charge

/-- SI radians-per-second readout of the angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedMagnitudeQuantity) : ℝ :=
  angularSpeedReadout UnitChoices.SI angularSpeed

/-- SI kilogram-meter-squared readout of the axial moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout UnitChoices.SI inertia

/-- SI kilogram-meter-squared-per-second angular-momentum readout. -/
def angularMomentumInKilogramMetersSquaredPerSecond
    (angularMomentum : AngularMomentumMagnitudeQuantity) : ℝ :=
  angularMomentumReadout UnitChoices.SI angularMomentum

/-- SI coulomb-meter-squared-per-second axial magnetic-moment readout. -/
def magneticMomentInCoulombMetersSquaredPerSecond
    (magneticMoment : MagneticMomentAxialQuantity) : ℝ :=
  magneticMomentReadout UnitChoices.SI magneticMoment

/-! ## Physical setup and primary-figure vocabulary -/

/-- The idealized distribution of the sphere's mass. -/
inductive MassDistributionModel where
  | uniformSolidSphere
  | other
  deriving DecidableEq, Repr

/-- The idealized distribution of the sphere's total charge. -/
inductive ChargeDistributionModel where
  | thinRingOnSurfaceAtEquator
  | other
  deriving DecidableEq, Repr

/-- Whether the local charge-to-mass ratio is uniform through the body. -/
inductive ChargeToMassRatioProfile where
  | spatiallyNonconstant
  | other
  deriving DecidableEq, Repr

/-- The geometry of the rotation axis relative to the charged ring. -/
inductive RotationAxisGeometry where
  | throughCenterPerpendicularToEquatorialPlane
  | other
  deriving DecidableEq, Repr

/-!
Qualitative data visible in the primary image.  The solid front portion of
the equatorial ring and the dashed hidden rear arc jointly identify a ring on
the sphere's equatorial surface.
-/
structure ChargedSphereFigure where
  blueSphereShown : Bool
  verticalCentralAxisShown : Bool
  solidFrontEquatorialRingShown : Bool
  dashedRearEquatorialArcShown : Bool
  rotationArrowShown : Bool

/-!
The physical system and its independent observables.  The ring radius is kept
separate from the sphere radius until the equatorial-surface geometry
predicate relates them.  Likewise, neither `gyromagneticFactor` nor any other
observable is defined from a displayed answer.
-/
structure ChargedSolidSphereSetup where
  massDistribution : MassDistributionModel
  chargeDistribution : ChargeDistributionModel
  chargeToMassRatioProfile : ChargeToMassRatioProfile
  rotationAxisGeometry : RotationAxisGeometry
  totalMass : MassQuantity
  sphereRadius : LengthQuantity
  chargeRingRadius : LengthQuantity
  totalCharge : ChargeQuantity
  angularSpeedMagnitude : AngularSpeedMagnitudeQuantity
  axialMomentOfInertia : MomentOfInertiaQuantity
  angularMomentumMagnitude : AngularMomentumMagnitudeQuantity
  magneticMomentAxialComponent : MagneticMomentAxialQuantity
  gyromagneticFactor : ℝ
  figure : ChargedSphereFigure

/-! ## Scenario, figure readouts, nondegeneracy, and governing laws -/

/-- The mass, charge, and axis idealizations stated in the problem. -/
structure MatchesSolidSphereWithEquatorialChargeRing
    (setup : ChargedSolidSphereSetup) : Prop where
  massFillsSolidSphere : setup.massDistribution = .uniformSolidSphere
  chargeIsEquatorialSurfaceRing :
    setup.chargeDistribution = .thinRingOnSurfaceAtEquator
  chargeToMassRatioVariesThroughSystem :
    setup.chargeToMassRatioProfile = .spatiallyNonconstant
  axisIsCentralAndNormal : setup.rotationAxisGeometry =
    .throughCenterPerpendicularToEquatorialPlane
  ringLiesOnSphereSurface : setup.chargeRingRadius = setup.sphereRadius
  gyromagneticFactorIsNotOne : setup.gyromagneticFactor ≠ 1

/-- Exact qualitative information transcribed from the supplied image. -/
structure MatchesPrimaryFigure (setup : ChargedSolidSphereSetup) : Prop where
  sphereIsShown : setup.figure.blueSphereShown = true
  verticalAxisIsShown : setup.figure.verticalCentralAxisShown = true
  frontRingIsShown : setup.figure.solidFrontEquatorialRingShown = true
  hiddenRearArcIsDashed : setup.figure.dashedRearEquatorialArcShown = true
  rotationIsShown : setup.figure.rotationArrowShown = true

/-!
Positivity and nondegeneracy assumptions needed to identify a unique
dimensionless factor.  In particular, both the charge and the rotation are
nonzero, so the gyromagnetic relation cannot degenerate to `0 = 0`.
-/
structure HasPhysicalNondegenerateParameters
    (setup : ChargedSolidSphereSetup) : Prop where
  massPositive : 0 < massInKilograms setup.totalMass
  sphereRadiusPositive : 0 < lengthInMeters setup.sphereRadius
  ringRadiusPositive : 0 < lengthInMeters setup.chargeRingRadius
  totalChargeNonzero : chargeInCoulombs setup.totalCharge ≠ 0
  angularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond setup.angularSpeedMagnitude
  momentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared setup.axialMomentOfInertia
  angularMomentumPositive :
    0 < angularMomentumInKilogramMetersSquaredPerSecond
      setup.angularMomentumMagnitude

/-!
The supplied solid-sphere formula `I = (2/5) M R^2`, required in every
coherent choice of units.  It contains no gyromagnetic-factor value.
-/
structure SatisfiesSolidSphereMomentOfInertiaLaw
    (setup : ChargedSolidSphereSetup) : Prop where
  inertiaOfSolidSphere : ∀ units : UnitChoices,
    momentOfInertiaReadout units setup.axialMomentOfInertia =
      (2 / 5 : ℝ) * massReadout units setup.totalMass *
        lengthReadout units setup.sphereRadius ^ 2

/-- The axial rigid-rotation law `L = I ω`. -/
structure SatisfiesRigidRotationAngularMomentumLaw
    (setup : ChargedSolidSphereSetup) : Prop where
  angularMomentumIsInertiaTimesAngularSpeed : ∀ units : UnitChoices,
    angularMomentumReadout units setup.angularMomentumMagnitude =
      momentOfInertiaReadout units setup.axialMomentOfInertia *
        angularSpeedReadout units setup.angularSpeedMagnitude

/-!
The magnetic moment of a thin rotating charge ring,
`μ = current * area = Q ω r^2 / 2`.  The radius here is the independent
ring radius; the scenario geometry, not this law, identifies it with `R`.
-/
structure SatisfiesRotatingChargeRingMagneticMomentLaw
    (setup : ChargedSolidSphereSetup) : Prop where
  magneticMomentOfRotatingRing : ∀ units : UnitChoices,
    magneticMomentReadout units setup.magneticMomentAxialComponent =
      chargeReadout units setup.totalCharge *
        angularSpeedReadout units setup.angularSpeedMagnitude *
        lengthReadout units setup.chargeRingRadius ^ 2 / 2

/-!
The classical relation supplied in the question,
`μ = g (Q/(2M)) L`, imposed in every coherent unit system.  It constrains the
independent factor but does not state the requested value.
-/
structure SatisfiesClassicalGyromagneticRelation
    (setup : ChargedSolidSphereSetup) : Prop where
  magneticMomentIsGTimesChargeToMassTimesAngularMomentum :
    ∀ units : UnitChoices,
      magneticMomentReadout units setup.magneticMomentAxialComponent =
        setup.gyromagneticFactor * chargeReadout units setup.totalCharge /
          (2 * massReadout units setup.totalMass) *
          angularMomentumReadout units setup.angularMomentumMagnitude

/-! ## Derived relations and displayed choices -/

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless numerical value printed for each answer choice. -/
def displayedGyromagneticFactor : AnswerChoice → ℝ
  | .A => 6 / 5
  | .B => 16 / 5
  | .C => 9 / 5
  | .D => 5 / 2

/-!
Combining the given solid-sphere inertia with rigid rotation yields
`L = (2/5) M R^2 ω` in SI readouts.  This is an intermediate mechanical
conclusion, not an assumption about `g`.
-/
lemma solid_sphere_angular_momentum_formula
    (setup : ChargedSolidSphereSetup)
    (hInertia : SatisfiesSolidSphereMomentOfInertiaLaw setup)
    (hRotation : SatisfiesRigidRotationAngularMomentumLaw setup) :
    angularMomentumInKilogramMetersSquaredPerSecond
        setup.angularMomentumMagnitude =
      (2 / 5 : ℝ) * massInKilograms setup.totalMass *
        lengthInMeters setup.sphereRadius ^ 2 *
        angularSpeedInRadiansPerSecond setup.angularSpeedMagnitude := by
  change
    angularMomentumReadout UnitChoices.SI setup.angularMomentumMagnitude =
      (2 / 5 : ℝ) * massReadout UnitChoices.SI setup.totalMass *
        lengthReadout UnitChoices.SI setup.sphereRadius ^ 2 *
        angularSpeedReadout UnitChoices.SI setup.angularSpeedMagnitude
  rw [hRotation.angularMomentumIsInertiaTimesAngularSpeed UnitChoices.SI,
    hInertia.inertiaOfSolidSphere UnitChoices.SI]

/-!
The equatorial-surface geometry specializes the rotating-ring law to the
sphere radius in SI readouts.  This is the electromagnetic intermediate used
when comparing magnetic moment with angular momentum.
-/
lemma equatorial_ring_magnetic_moment_formula
    (setup : ChargedSolidSphereSetup)
    (hScenario : MatchesSolidSphereWithEquatorialChargeRing setup)
    (hRing : SatisfiesRotatingChargeRingMagneticMomentLaw setup) :
    magneticMomentInCoulombMetersSquaredPerSecond
        setup.magneticMomentAxialComponent =
      chargeInCoulombs setup.totalCharge *
        angularSpeedInRadiansPerSecond setup.angularSpeedMagnitude *
        lengthInMeters setup.sphereRadius ^ 2 / 2 := by
  change
    magneticMomentReadout UnitChoices.SI setup.magneticMomentAxialComponent =
      chargeReadout UnitChoices.SI setup.totalCharge *
        angularSpeedReadout UnitChoices.SI setup.angularSpeedMagnitude *
        lengthReadout UnitChoices.SI setup.sphereRadius ^ 2 / 2
  rw [hRing.magneticMomentOfRotatingRing UnitChoices.SI,
    hScenario.ringLiesOnSphereSurface]

/-!
Comparison of the independent mechanical and electromagnetic laws with the
given gyromagnetic relation forces `g = 5/2`.  Choice D is therefore the
unique displayed match.

This is the formal target corresponding to
`thm:physics:phyx_mini_0563:target`.
-/
theorem gyromagnetic_factor_of_solid_sphere_with_equatorial_charge_ring
    (setup : ChargedSolidSphereSetup)
    (hScenario : MatchesSolidSphereWithEquatorialChargeRing setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalNondegenerateParameters setup)
    (hInertia : SatisfiesSolidSphereMomentOfInertiaLaw setup)
    (hRotation : SatisfiesRigidRotationAngularMomentumLaw setup)
    (hRing : SatisfiesRotatingChargeRingMagneticMomentLaw setup)
    (hGyromagnetic : SatisfiesClassicalGyromagneticRelation setup) :
    setup.gyromagneticFactor = (5 / 2 : ℝ) ∧
      displayedGyromagneticFactor .D = setup.gyromagneticFactor ∧
      ∀ choice : AnswerChoice,
        displayedGyromagneticFactor choice = setup.gyromagneticFactor →
          choice = .D := by
  have hAngularMomentum :=
    solid_sphere_angular_momentum_formula setup hInertia hRotation
  have hMagneticMoment :=
    equatorial_ring_magnetic_moment_formula setup hScenario hRing
  have hGyromagneticSI :=
    hGyromagnetic.magneticMomentIsGTimesChargeToMassTimesAngularMomentum
      UnitChoices.SI
  change
    magneticMomentInCoulombMetersSquaredPerSecond
        setup.magneticMomentAxialComponent =
      setup.gyromagneticFactor * chargeInCoulombs setup.totalCharge /
        (2 * massInKilograms setup.totalMass) *
        angularMomentumInKilogramMetersSquaredPerSecond
          setup.angularMomentumMagnitude at hGyromagneticSI
  rw [hMagneticMoment, hAngularMomentum] at hGyromagneticSI
  have hMassNonzero :
      massInKilograms setup.totalMass ≠ 0 :=
    ne_of_gt hPhysical.massPositive
  field_simp [hMassNonzero] at hGyromagneticSI
  let commonFactor : ℝ :=
    chargeInCoulombs setup.totalCharge *
      angularSpeedInRadiansPerSecond setup.angularSpeedMagnitude *
      lengthInMeters setup.sphereRadius ^ 2
  have hCommonFactorNonzero : commonFactor ≠ 0 := by
    dsimp [commonFactor]
    exact
      mul_ne_zero
        (mul_ne_zero hPhysical.totalChargeNonzero
          (ne_of_gt hPhysical.angularSpeedPositive))
        (pow_ne_zero 2 (ne_of_gt hPhysical.sphereRadiusPositive))
  have hScaledFactor :
      commonFactor * 5 =
        commonFactor * (2 * setup.gyromagneticFactor) := by
    simpa only [commonFactor, mul_assoc] using hGyromagneticSI
  have hFactorEquation : (5 : ℝ) = 2 * setup.gyromagneticFactor :=
    mul_left_cancel₀ hCommonFactorNonzero hScaledFactor
  have hFactor : setup.gyromagneticFactor = (5 / 2 : ℝ) := by
    norm_num at hFactorEquation ⊢
    linarith
  refine ⟨hFactor, ?_, ?_⟩
  · norm_num [displayedGyromagneticFactor, hFactor]
  · intro choice hChoice
    cases choice with
    | A => norm_num [displayedGyromagneticFactor, hFactor] at hChoice
    | B => norm_num [displayedGyromagneticFactor, hFactor] at hChoice
    | C => norm_num [displayedGyromagneticFactor, hFactor] at hChoice
    | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0563
