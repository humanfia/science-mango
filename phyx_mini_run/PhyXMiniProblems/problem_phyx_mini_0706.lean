import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0706

open Dimension

/-!
# A falling bucket driving a solid cylinder

A `2.0 kg` bucket hangs from a massless string wrapped around a `1.0 kg`,
`4.0 cm`-diameter cylinder.  The cylinder turns about its central axle while
the bucket falls from rest through `1.0 m`.

Physical quantities below use Physlib's unit-independent `Dimensionful`
representation.  Real numbers occur only as signed coordinate components,
coherent unit readouts, or dimensionless numerical data printed with the
exercise.
-/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed vertical coordinate. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed linear velocity component. -/
abbrev SignedSpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative linear-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Moment of inertia has dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- Angular acceleration has inverse-time-squared dimension because radians
are dimensionless. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a nonnegative length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (position : SignedLengthQuantity) : ℝ :=
  (position {UnitChoices.SI with length := unit}).val

/-- Read a duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed speed in coherent selected length and time units. -/
def signedSpeedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SignedSpeedQuantity) : ℝ :=
  (speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read an acceleration magnitude in coherent selected units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a force magnitude in coherent selected mechanical units. -/
def forceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceQuantity) : ℝ :=
  ((force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read angular acceleration in inverse square units of the selected time
unit. -/
def angularAccelerationReadout
    (timeUnit : TimeUnit) (acceleration : AngularAccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- SI kilogram readout of a mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- SI meter readout of a nonnegative length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- SI meter readout of a signed vertical coordinate. -/
def signedLengthInMeters (position : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters position

/-- SI second readout of a duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- SI meter-per-second readout of a signed velocity. -/
def signedSpeedInMetersPerSecond (speed : SignedSpeedQuantity) : ℝ :=
  signedSpeedReadout LengthUnit.meters TimeUnit.seconds speed

/-- SI meter-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- How the cylinder's mass is idealized. -/
inductive CylinderMassModel where
  | uniformSolid
  | other
  deriving DecidableEq, Repr

/-- The mass model of the connecting string. -/
inductive StringMassModel where
  | massless
  | other
  deriving DecidableEq, Repr

/-- Where the rotation axle passes through the cylinder. -/
inductive AxleLocation where
  | throughCenter
  | other
  deriving DecidableEq, Repr

/-- The resistance supplied by the axle. -/
inductive AxleResistanceModel where
  | negligible
  | other
  deriving DecidableEq, Repr

/-- Whether the string slides relative to the cylinder surface. -/
inductive StringCylinderContact where
  | noSlip
  | other
  deriving DecidableEq, Repr

/-- Text or arrow labels visible in the supplied figure. -/
inductive FigureLabel where
  | verticalAxisY
  | cylinderRadiusR
  | cylinderMassM
  | bucketMassm
  | initialPositionY0
  | finalPositionY1
  | initialVelocityV0
  | bucketAccelerationA
  | angularAccelerationAlpha
  | axle
  deriving DecidableEq, Repr

/-- Qualitative geometry transcribed from the primary image. -/
structure SuppliedBucketCylinderFigure where
  showsLabel : FigureLabel → Bool
  showsStringWrappedAroundCylinder : Bool
  showsBucketBelowCylinder : Bool
  showsAxleAtCylinderCenter : Bool
  showsBucketAccelerationDownward : Bool
  showsCylinderRotationArrow : Bool
  floorIsAtFinalPosition : Bool

/-!
Independent physical quantities and response fields for the modeled motion.
The acceleration, tension, inertia, angular acceleration, and fall time are
not defined from the requested answer; the governing-law predicates below
constrain them.
-/
structure BucketCylinderSetup where
  bucketMass : MassQuantity
  cylinderMass : MassQuantity
  cylinderRadius : LengthQuantity
  cylinderDiameter : LengthQuantity
  initialVerticalPosition : SignedLengthQuantity
  floorVerticalPosition : SignedLengthQuantity
  initialVerticalVelocity : SignedSpeedQuantity
  gravitationalAcceleration : AccelerationQuantity
  bucketDownwardAcceleration : AccelerationQuantity
  cylinderAngularAcceleration : AngularAccelerationQuantity
  stringTension : ForceQuantity
  cylinderMomentOfInertia : MomentOfInertiaQuantity
  fallTime : TimeQuantity
  cylinderMassModel : CylinderMassModel
  stringMassModel : StringMassModel
  axleLocation : AxleLocation
  axleResistanceModel : AxleResistanceModel
  stringCylinderContact : StringCylinderContact
  figure : SuppliedBucketCylinderFigure

/-!
Numerical data and image readouts supplied by the exercise.  The source gives
the diameter as `4.0 cm`, while the image additionally labels the radius as
`2.0 cm`.  The unit-independent statement of release from rest is included
for every coherent pair of length and time units.
-/
structure MatchesProblemAndFigureReadouts
    (setup : BucketCylinderSetup) : Prop where
  bucketMassKilograms : massInKilograms setup.bucketMass = 2.0
  cylinderMassKilograms : massInKilograms setup.cylinderMass = 1.0
  cylinderRadiusMeters : lengthInMeters setup.cylinderRadius = 0.02
  cylinderDiameterMeters : lengthInMeters setup.cylinderDiameter = 0.04
  initialPositionMeters :
    signedLengthInMeters setup.initialVerticalPosition = 1.0
  floorPositionMeters :
    signedLengthInMeters setup.floorVerticalPosition = 0
  releasedFromRest :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      signedSpeedReadout lengthUnit timeUnit
        setup.initialVerticalVelocity = 0
  cylinderIsUniformSolid : setup.cylinderMassModel = .uniformSolid
  stringIsMassless : setup.stringMassModel = .massless
  axlePassesThroughCenter : setup.axleLocation = .throughCenter
  axleResistanceIsNegligible :
    setup.axleResistanceModel = .negligible
  stringDoesNotSlip : setup.stringCylinderContact = .noSlip
  everyPrintedLabelIsShown :
    ∀ label, setup.figure.showsLabel label = true
  wrappedStringReadout :
    setup.figure.showsStringWrappedAroundCylinder = true
  bucketBelowCylinderReadout :
    setup.figure.showsBucketBelowCylinder = true
  centralAxleReadout : setup.figure.showsAxleAtCylinderCenter = true
  downwardAccelerationReadout :
    setup.figure.showsBucketAccelerationDownward = true
  rotationArrowReadout : setup.figure.showsCylinderRotationArrow = true
  floorEndpointReadout : setup.figure.floorIsAtFinalPosition = true

/-- The standard near-Earth gravitational field used for the numerical
multiple-choice evaluation. -/
structure UsesStandardEarthGravity (setup : BucketCylinderSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 9.8

/-- Positivity and nondegeneracy conditions for the physical parameters. -/
structure HasPhysicalParameters (setup : BucketCylinderSetup) : Prop where
  bucketMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.bucketMass
  cylinderMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.cylinderMass
  cylinderRadiusPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.cylinderRadius
  cylinderDiameterPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.cylinderDiameter
  gravityPositive :
    ∀ lengthUnit timeUnit,
      0 < accelerationReadout lengthUnit timeUnit
        setup.gravitationalAcceleration
  initialPositionAboveFloor :
    ∀ lengthUnit,
      signedLengthReadout lengthUnit setup.floorVerticalPosition <
        signedLengthReadout lengthUnit setup.initialVerticalPosition
  fallTimePositive :
    ∀ timeUnit, 0 < timeReadout timeUnit setup.fallTime

/-- The diameter is twice the radius in every length unit. -/
structure SatisfiesCylinderGeometry (setup : BucketCylinderSetup) : Prop where
  diameterIsTwiceRadius :
    ∀ lengthUnit,
      lengthReadout lengthUnit setup.cylinderDiameter =
        2 * lengthReadout lengthUnit setup.cylinderRadius

/-- Axial moment of inertia of a uniform solid cylinder,
`I = (1/2) M R²`. -/
structure SatisfiesUniformSolidCylinderInertiaLaw
    (setup : BucketCylinderSetup) : Prop where
  axialMomentOfInertia :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.cylinderMomentOfInertia =
        (1 / 2 : ℝ) * massReadout massUnit setup.cylinderMass *
          (lengthReadout lengthUnit setup.cylinderRadius) ^ 2

/-!
Governing scalar dynamics, with downward positive for the bucket and the
corresponding rotation direction positive for the cylinder:

* `m g - T = m a` for the bucket;
* `T R = I α` about the central axle;
* `a = R α` for a taut, non-slipping string.

These laws do not state the requested acceleration or fall time.
-/
structure SatisfiesBucketCylinderDynamics
    (setup : BucketCylinderSetup) : Prop where
  bucketNewtonSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.bucketMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration -
          forceReadout massUnit lengthUnit timeUnit setup.stringTension =
        massReadout massUnit setup.bucketMass *
          accelerationReadout lengthUnit timeUnit
            setup.bucketDownwardAcceleration
  cylinderRotationalSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit setup.stringTension *
          lengthReadout lengthUnit setup.cylinderRadius =
        momentOfInertiaReadout massUnit lengthUnit
            setup.cylinderMomentOfInertia *
          angularAccelerationReadout timeUnit
            setup.cylinderAngularAcceleration
  noSlipTangentialCoupling :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationReadout lengthUnit timeUnit
          setup.bucketDownwardAcceleration =
        lengthReadout lengthUnit setup.cylinderRadius *
          angularAccelerationReadout timeUnit
            setup.cylinderAngularAcceleration

/-!
The vertical coordinate is positive upward.  With a constant downward
acceleration magnitude `a`, the endpoint equation is

`y₁ = y₀ + v₀ t - (1/2) a t²`.

This generic kinematic law constrains the response field `fallTime`; it does
not prescribe its solved value.
-/
structure SatisfiesConstantAccelerationKinematics
    (setup : BucketCylinderSetup) : Prop where
  floorEndpointEquation :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      signedLengthReadout lengthUnit setup.floorVerticalPosition =
        signedLengthReadout lengthUnit setup.initialVerticalPosition +
          signedSpeedReadout lengthUnit timeUnit
              setup.initialVerticalVelocity *
            timeReadout timeUnit setup.fallTime -
          (1 / 2 : ℝ) *
            accelerationReadout lengthUnit timeUnit
              setup.bucketDownwardAcceleration *
            (timeReadout timeUnit setup.fallTime) ^ 2

/-!
Eliminating tension and angular acceleration from the three dynamics laws,
then using the solid-cylinder inertia law, gives the constant downward
acceleration.  This is an intermediate consequence, not a premise.
-/
lemma bucketDownwardAcceleration_formula
    (setup : BucketCylinderSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesUniformSolidCylinderInertiaLaw setup)
    (hDynamics : SatisfiesBucketCylinderDynamics setup) :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      accelerationReadout lengthUnit timeUnit
          setup.bucketDownwardAcceleration =
        massReadout massUnit setup.bucketMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration /
          (massReadout massUnit setup.bucketMass +
            massReadout massUnit setup.cylinderMass / 2) := by
  intro massUnit lengthUnit timeUnit
  have hBucketMass :=
    hPhysical.bucketMassPositive massUnit
  have hCylinderMass :=
    hPhysical.cylinderMassPositive massUnit
  have hRadius :=
    hPhysical.cylinderRadiusPositive lengthUnit
  have hNewton :=
    hDynamics.bucketNewtonSecondLaw massUnit lengthUnit timeUnit
  have hTorque :=
    hDynamics.cylinderRotationalSecondLaw massUnit lengthUnit timeUnit
  have hNoSlip :=
    hDynamics.noSlipTangentialCoupling lengthUnit timeUnit
  rw [hInertia.axialMomentOfInertia massUnit lengthUnit] at hTorque
  have hTension :
      forceReadout massUnit lengthUnit timeUnit setup.stringTension =
        massReadout massUnit setup.cylinderMass / 2 *
          accelerationReadout lengthUnit timeUnit
            setup.bucketDownwardAcceleration := by
    apply (mul_right_cancel₀ (ne_of_gt hRadius))
    linear_combination hTorque -
      (massReadout massUnit setup.cylinderMass / 2 *
        lengthReadout lengthUnit setup.cylinderRadius) * hNoSlip
  rw [hTension] at hNewton
  have hEffectiveMass :
      0 < massReadout massUnit setup.bucketMass +
        massReadout massUnit setup.cylinderMass / 2 := by
    nlinarith
  apply (eq_div_iff (ne_of_gt hEffectiveMass)).2
  nlinarith

/-!
The positive solution of the endpoint kinematics is

`t = sqrt (2 h (m + M/2) / (m g))`,

where `h = y₀ - y₁`.  The cylinder radius cancels after the no-slip and
solid-cylinder laws are combined.
-/
lemma fallTime_formula
    (setup : BucketCylinderSetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesUniformSolidCylinderInertiaLaw setup)
    (hDynamics : SatisfiesBucketCylinderDynamics setup)
    (hKinematics : SatisfiesConstantAccelerationKinematics setup) :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      timeReadout timeUnit setup.fallTime =
        Real.sqrt
          (2 *
            (signedLengthReadout lengthUnit setup.initialVerticalPosition -
              signedLengthReadout lengthUnit setup.floorVerticalPosition) *
            (massReadout massUnit setup.bucketMass +
              massReadout massUnit setup.cylinderMass / 2) /
            (massReadout massUnit setup.bucketMass *
              accelerationReadout lengthUnit timeUnit
                setup.gravitationalAcceleration)) := by
  intro massUnit lengthUnit timeUnit
  have hBucketMass :=
    hPhysical.bucketMassPositive massUnit
  have hCylinderMass :=
    hPhysical.cylinderMassPositive massUnit
  have hGravity :=
    hPhysical.gravityPositive lengthUnit timeUnit
  have hFallTime :=
    hPhysical.fallTimePositive timeUnit
  have hHeight :=
    hPhysical.initialPositionAboveFloor lengthUnit
  have hAcceleration :=
    bucketDownwardAcceleration_formula setup hPhysical hInertia hDynamics
      massUnit lengthUnit timeUnit
  have hKinematic :=
    hKinematics.floorEndpointEquation lengthUnit timeUnit
  rw [hReadouts.releasedFromRest lengthUnit timeUnit] at hKinematic
  have hEffectiveMass :
      0 < massReadout massUnit setup.bucketMass +
        massReadout massUnit setup.cylinderMass / 2 := by
    nlinarith
  have hAccelerationTimesEffectiveMass :
      accelerationReadout lengthUnit timeUnit
            setup.bucketDownwardAcceleration *
          (massReadout massUnit setup.bucketMass +
            massReadout massUnit setup.cylinderMass / 2) =
        massReadout massUnit setup.bucketMass *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration :=
    (eq_div_iff (ne_of_gt hEffectiveMass)).mp hAcceleration
  have hMotion :
      accelerationReadout lengthUnit timeUnit
            setup.bucketDownwardAcceleration *
          (timeReadout timeUnit setup.fallTime) ^ 2 =
        2 *
          (signedLengthReadout lengthUnit setup.initialVerticalPosition -
            signedLengthReadout lengthUnit setup.floorVerticalPosition) := by
    nlinarith
  have hMassGravity :
      0 <
        massReadout massUnit setup.bucketMass *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration :=
    mul_pos hBucketMass hGravity
  have hTimeSquared :
      (timeReadout timeUnit setup.fallTime) ^ 2 =
        2 *
            (signedLengthReadout lengthUnit setup.initialVerticalPosition -
              signedLengthReadout lengthUnit setup.floorVerticalPosition) *
            (massReadout massUnit setup.bucketMass +
              massReadout massUnit setup.cylinderMass / 2) /
          (massReadout massUnit setup.bucketMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration) := by
    apply (eq_div_iff (ne_of_gt hMassGravity)).2
    calc
      (timeReadout timeUnit setup.fallTime) ^ 2 *
            (massReadout massUnit setup.bucketMass *
              accelerationReadout lengthUnit timeUnit
                setup.gravitationalAcceleration) =
          (timeReadout timeUnit setup.fallTime) ^ 2 *
            (accelerationReadout lengthUnit timeUnit
                setup.bucketDownwardAcceleration *
              (massReadout massUnit setup.bucketMass +
                massReadout massUnit setup.cylinderMass / 2)) := by
                  rw [hAccelerationTimesEffectiveMass]
      _ =
          (accelerationReadout lengthUnit timeUnit
              setup.bucketDownwardAcceleration *
            (timeReadout timeUnit setup.fallTime) ^ 2) *
              (massReadout massUnit setup.bucketMass +
                massReadout massUnit setup.cylinderMass / 2) := by ring
      _ =
          2 *
              (signedLengthReadout lengthUnit
                  setup.initialVerticalPosition -
                signedLengthReadout lengthUnit setup.floorVerticalPosition) *
            (massReadout massUnit setup.bucketMass +
              massReadout massUnit setup.cylinderMass / 2) := by
                rw [hMotion]
  rw [← hTimeSquared, Real.sqrt_sq (le_of_lt hFallTime)]

/-- Answer labels displayed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Times printed beside the answer choices, in seconds. -/
def displayedTimeInSeconds : AnswerChoice → ℝ
  | .A => 0.55
  | .B => 0.45
  | .C => 0.50
  | .D => 0.40

/-- Dataset metadata; it is not a premise of the theorem. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- The physical fall time is strictly closer to one displayed value than to
every other displayed value. -/
def IsUniqueClosestDisplayedTime
    (setup : BucketCylinderSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |timeInSeconds setup.fallTime - displayedTimeInSeconds choice| <
      |timeInSeconds setup.fallTime - displayedTimeInSeconds other|

/-!
For the supplied SI readouts and standard `g = 9.8 m/s²`, the exact modeled
fall time is given by the derived square-root formula and is uniquely closest
to `0.50 s`, choice `C`.

This is the formal target corresponding to
`thm:physics:phyx_mini_0706:target`.
-/
theorem problem_phyx_mini_0706
    (setup : BucketCylinderSetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hGravity : UsesStandardEarthGravity setup)
    (hPhysical : HasPhysicalParameters setup)
    (hGeometry : SatisfiesCylinderGeometry setup)
    (hInertia : SatisfiesUniformSolidCylinderInertiaLaw setup)
    (hDynamics : SatisfiesBucketCylinderDynamics setup)
    (hKinematics : SatisfiesConstantAccelerationKinematics setup) :
    (timeInSeconds setup.fallTime =
      Real.sqrt
        (2 *
          (signedLengthInMeters setup.initialVerticalPosition -
            signedLengthInMeters setup.floorVerticalPosition) *
          (massInKilograms setup.bucketMass +
            massInKilograms setup.cylinderMass / 2) /
          (massInKilograms setup.bucketMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration))) ∧
      IsUniqueClosestDisplayedTime setup .C := by
  have hFormula :=
    fallTime_formula setup hReadouts hPhysical hInertia hDynamics hKinematics
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  constructor
  · exact hFormula
  · have hDuration :
        timeInSeconds setup.fallTime = Real.sqrt (25 / 98) := by
      have hInitial := hReadouts.initialPositionMeters
      have hFloor := hReadouts.floorPositionMeters
      have hBucketMass := hReadouts.bucketMassKilograms
      have hCylinderMass := hReadouts.cylinderMassKilograms
      have hGravitySI := hGravity.gravitationalAccelerationSI
      change
        signedLengthReadout LengthUnit.meters
            setup.initialVerticalPosition = 1.0 at hInitial
      change
        signedLengthReadout LengthUnit.meters
            setup.floorVerticalPosition = 0 at hFloor
      change
        massReadout MassUnit.kilograms setup.bucketMass = 2.0 at hBucketMass
      change
        massReadout MassUnit.kilograms setup.cylinderMass = 1.0 at hCylinderMass
      change
        accelerationReadout LengthUnit.meters TimeUnit.seconds
            setup.gravitationalAcceleration = 9.8 at hGravitySI
      change timeReadout TimeUnit.seconds setup.fallTime = Real.sqrt (25 / 98)
      rw [hInitial, hFloor, hBucketMass, hCylinderMass, hGravitySI] at hFormula
      norm_num at hFormula ⊢
      exact hFormula
    unfold IsUniqueClosestDisplayedTime
    intro other hOther
    rw [hDuration]
    have hRadicandNonnegative : (0 : ℝ) ≤ 25 / 98 := by
      norm_num
    have hSqrtSquared : (Real.sqrt (25 / 98) : ℝ) ^ 2 = 25 / 98 :=
      Real.sq_sqrt hRadicandNonnegative
    have hSqrtNonnegative : (0 : ℝ) ≤ Real.sqrt (25 / 98) :=
      Real.sqrt_nonneg _
    have hLower : (1 / 2 : ℝ) < Real.sqrt (25 / 98) := by
      nlinarith
    have hUpper : Real.sqrt (25 / 98) < (21 / 40 : ℝ) := by
      nlinarith
    cases other with
    | A =>
        simp only [displayedTimeInSeconds]
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        linarith
    | B =>
        simp only [displayedTimeInSeconds]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
    | C =>
        exact (hOther rfl).elim
    | D =>
        simp only [displayedTimeInSeconds]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith

end PhyXMiniProblems.ProblemPhyXMini0706
