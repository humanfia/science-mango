import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Mass of a uniform-disk wheel driven by a descending object

A thin, light wire is wrapped around the rim of a uniform disk.  The disk
rotates without axle friction about the horizontal axis through its center,
while a `4.20 kg` object suspended from the wire descends from rest.  The disk
radius is `0.280 m`, and the object descends `3.00 m` in `2.00 s` with constant
acceleration.

Physical masses, lengths, times, speeds, accelerations, forces, moments of
inertia, and angular accelerations are represented by unit-independent
Physlib quantities.  Real numbers below are only coherent unit readouts or
dimensionless numerical data printed with the exercise.

Assumption/target boundary:

* `MatchesProblemReadouts` records the prose data and idealizations.
* `MatchesPrimaryFigure` records only the visible wheel--wire--block geometry.
* `UsesStandardEarthGravity` supplies the numerical environmental value of
  `g` needed to evaluate the multiple-choice answer.
* `UsesTautNoSlipUnwinding` makes explicit the no-slip convention needed to
  couple the wire's linear motion to the wheel's rotation; it is not claimed
  as a printed source readout.
* the governing `Satisfies...` predicates state generic inertia,
  translational dynamics, rotational dynamics, no-slip coupling, and
  constant-acceleration kinematics.
* there are no previous-part results.
* the derived acceleration, the wheel mass, and answer choice `B` occur only
  in conclusions and in the separate displayed-answer table.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0771

open Dimension

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- The physical dimension of speed, `L T⁻¹`. -/
def speedDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * accelerationDimension

/-- The physical dimension of axial moment of inertia, `M L²`. -/
def momentOfInertiaDimension : Dimension := M𝓭 * L𝓭 * L𝓭

/-- Angular acceleration has physical dimension `T⁻²`; radians are
dimensionless. -/
def angularAccelerationDimension : Dimension := T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length or distance. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative speed in the downward direction chosen as positive. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative downward linear-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative tension-force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative scalar moment of inertia about the fixed axle. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative angular acceleration in the sense in which the wire
unwinds. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim angularAccelerationDimension NNReal)

/-- Read a mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a duration in a selected time unit. -/
def timeReadout (unit : TimeUnit) (duration : TimeQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a linear acceleration in coherent selected units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a force in coherent selected mechanical units. -/
def forceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceQuantity) : ℝ :=
  ((force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an axial moment of inertia in coherent mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read angular acceleration in inverse square units of a selected time
unit. -/
def angularAccelerationReadout
    (timeUnit : TimeUnit) (acceleration : AngularAccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- SI meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- SI second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  timeReadout TimeUnit.seconds duration

/-- SI meter-per-second readout of a speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- SI meter-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Physical and primary-figure vocabulary -/

/-- Idealized distribution of the wheel's mass. -/
inductive WheelMassDistribution where
  | uniformDisk
  | other
  deriving DecidableEq, Repr

/-- Mass idealization of the wire. -/
inductive WireMassModel where
  | thinAndLight
  | other
  deriving DecidableEq, Repr

/-- Route taken by the wire at the wheel. -/
inductive WireRouting where
  | wrappedAroundRim
  | other
  deriving DecidableEq, Repr

/-- Location of the wheel's fixed axle. -/
inductive AxleLocation where
  | throughWheelCenter
  | other
  deriving DecidableEq, Repr

/-- Orientation of the wheel's fixed axle. -/
inductive AxleOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Whether the wheel's axle moves relative to the laboratory. -/
inductive AxleMotionModel where
  | stationary
  | other
  deriving DecidableEq, Repr

/-- Dissipative resistance at the fixed axle. -/
inductive AxleResistanceModel where
  | frictionless
  | other
  deriving DecidableEq, Repr

/-- Contact model between the wrapped wire and the wheel rim. -/
inductive WireWheelContact where
  | tautNoSlip
  | other
  deriving DecidableEq, Repr

/-- Time dependence of the suspended object's downward acceleration. -/
inductive MotionProfile where
  | constantAcceleration
  | other
  deriving DecidableEq, Repr

/-- How the motion begins. -/
inductive ReleaseCondition where
  | fromRest
  | other
  deriving DecidableEq, Repr

/-- Individually visible objects or marks in primary image `771.png`. -/
inductive FigureFeature where
  | circularWheel
  | centralAxleDot
  | verticalWireSegment
  | suspendedBlock
  deriving DecidableEq, Fintype, Repr

/-- Structured transcription of the unlabeled primary raster. -/
structure WheelAndBlockFigure where
  showsFeature : FigureFeature → Bool
  wheelIsAboveBlock : Bool
  wireMeetsRightSideOfRim : Bool
  wireSegmentIsVertical : Bool
  wireConnectsRimToBlock : Bool
  containsTextOrArrowLabels : Bool

/-!
The physical response fields are independent quantities.  In particular,
`wheelMass`, `downwardAcceleration`, `wireTension`, `wheelMomentOfInertia`,
and `wheelAngularAcceleration` are not defined from the requested answer.
-/
structure WheelAndBlockSetup where
  suspendedObjectMass : MassQuantity
  wheelMass : MassQuantity
  wheelRadius : LengthQuantity
  descentDistance : LengthQuantity
  elapsedTime : TimeQuantity
  initialDownwardSpeed : SpeedQuantity
  gravitationalAcceleration : AccelerationQuantity
  downwardAcceleration : AccelerationQuantity
  wireTension : ForceQuantity
  wheelMomentOfInertia : MomentOfInertiaQuantity
  wheelAngularAcceleration : AngularAccelerationQuantity
  wheelMassDistribution : WheelMassDistribution
  wireMassModel : WireMassModel
  wireRouting : WireRouting
  axleLocation : AxleLocation
  axleOrientation : AxleOrientation
  axleMotionModel : AxleMotionModel
  axleResistanceModel : AxleResistanceModel
  wireWheelContact : WireWheelContact
  motionProfile : MotionProfile
  releaseCondition : ReleaseCondition
  figure : WheelAndBlockFigure

/-! ## Source data, figure evidence, and nondegeneracy -/

/-- Numerical data and qualitative idealizations stated in the prose. -/
structure MatchesProblemReadouts (setup : WheelAndBlockSetup) : Prop where
  suspendedMassKilograms :
    massInKilograms setup.suspendedObjectMass = 4.20
  wheelRadiusMeters : lengthInMeters setup.wheelRadius = 0.280
  descentDistanceMeters : lengthInMeters setup.descentDistance = 3.00
  elapsedTimeSeconds : timeInSeconds setup.elapsedTime = 2.00
  releasedWithZeroSpeed :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.initialDownwardSpeed = 0
  wheelIsUniformDisk : setup.wheelMassDistribution = .uniformDisk
  wireIsThinAndLight : setup.wireMassModel = .thinAndLight
  wireIsWrappedAroundRim : setup.wireRouting = .wrappedAroundRim
  axlePassesThroughCenter : setup.axleLocation = .throughWheelCenter
  axleIsHorizontal : setup.axleOrientation = .horizontal
  axleIsStationary : setup.axleMotionModel = .stationary
  axleIsFrictionless : setup.axleResistanceModel = .frictionless
  accelerationIsConstant : setup.motionProfile = .constantAcceleration
  systemReleasedFromRest : setup.releaseCondition = .fromRest

/-- Literal qualitative evidence transcribed from primary image `771.png`.
The raster contains no printed symbolic or numerical labels. -/
structure MatchesPrimaryFigure (setup : WheelAndBlockSetup) : Prop where
  everyFeatureShown : ∀ feature, setup.figure.showsFeature feature = true
  wheelAboveBlock : setup.figure.wheelIsAboveBlock = true
  wireAtRightRim : setup.figure.wireMeetsRightSideOfRim = true
  verticalWire : setup.figure.wireSegmentIsVertical = true
  connectedWheelAndBlock : setup.figure.wireConnectsRimToBlock = true
  noTextOrArrowLabels : setup.figure.containsTextOrArrowLabels = false

/-- Standard near-Earth gravitational acceleration used in the numerical
multiple-choice evaluation. -/
structure UsesStandardEarthGravity (setup : WheelAndBlockSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 9.8

/-- Standard ideal-wire contact convention used to turn the observed wrapped
wire into the kinematic coupling `a = R α`.  The exercise does not print this
convention, so it is kept separate from `MatchesProblemReadouts`. -/
structure UsesTautNoSlipUnwinding (setup : WheelAndBlockSetup) : Prop where
  contactModel : setup.wireWheelContact = .tautNoSlip

/-- Positivity and nondegeneracy of the physical parameters needed when the
governing equations are solved. -/
structure HasPhysicalParameters (setup : WheelAndBlockSetup) : Prop where
  suspendedMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.suspendedObjectMass
  wheelMassPositive :
    ∀ massUnit, 0 < massReadout massUnit setup.wheelMass
  wheelRadiusPositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.wheelRadius
  descentDistancePositive :
    ∀ lengthUnit, 0 < lengthReadout lengthUnit setup.descentDistance
  elapsedTimePositive :
    ∀ timeUnit, 0 < timeReadout timeUnit setup.elapsedTime
  gravitationalAccelerationPositive :
    ∀ lengthUnit timeUnit,
      0 < accelerationReadout lengthUnit timeUnit
        setup.gravitationalAcceleration
  downwardAccelerationPositive :
    ∀ lengthUnit timeUnit,
      0 < accelerationReadout lengthUnit timeUnit setup.downwardAcceleration

/-! ## Governing physical laws -/

/-- Axial moment of inertia of a uniform disk about the central axis normal
to its plane: `I = (1/2) M R²`. -/
structure SatisfiesUniformDiskInertiaLaw
    (setup : WheelAndBlockSetup) : Prop where
  axialMomentOfInertia :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.wheelMomentOfInertia =
        (1 / 2 : ℝ) * massReadout massUnit setup.wheelMass *
          (lengthReadout lengthUnit setup.wheelRadius) ^ 2

/-!
Downward is positive for the suspended object, and positive wheel rotation is
the direction in which the wire unwinds:

* `m g - T = m a` for the suspended object;
* `T R = I α` about the wheel's central axle;
* `a = R α` for a taut wire that does not slip on the rim.

None of these laws states the requested wheel mass.
-/
structure SatisfiesCoupledTranslationRotationDynamics
    (setup : WheelAndBlockSetup) : Prop where
  suspendedObjectNewtonSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.suspendedObjectMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration -
          forceReadout massUnit lengthUnit timeUnit setup.wireTension =
        massReadout massUnit setup.suspendedObjectMass *
          accelerationReadout lengthUnit timeUnit setup.downwardAcceleration
  wheelRotationalSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit setup.wireTension *
          lengthReadout lengthUnit setup.wheelRadius =
        momentOfInertiaReadout massUnit lengthUnit
            setup.wheelMomentOfInertia *
          angularAccelerationReadout timeUnit setup.wheelAngularAcceleration
  noSlipTangentialCoupling :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationReadout lengthUnit timeUnit setup.downwardAcceleration =
        lengthReadout lengthUnit setup.wheelRadius *
          angularAccelerationReadout timeUnit setup.wheelAngularAcceleration

/-!
With downward positive and constant acceleration, the measured endpoint obeys

`distance = initialSpeed * time + (1/2) * acceleration * time²`.

This is a generic kinematic law, not the solved acceleration or wheel mass.
-/
structure SatisfiesConstantAccelerationKinematics
    (setup : WheelAndBlockSetup) : Prop where
  descentEndpointEquation :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      lengthReadout lengthUnit setup.descentDistance =
        speedReadout lengthUnit timeUnit setup.initialDownwardSpeed *
            timeReadout timeUnit setup.elapsedTime +
          (1 / 2 : ℝ) *
            accelerationReadout lengthUnit timeUnit
              setup.downwardAcceleration *
            (timeReadout timeUnit setup.elapsedTime) ^ 2

/-! ## Derived relations and multiple-choice target -/

/-- Solving the constant-acceleration endpoint equation for the downward
acceleration.  This is an intermediate conclusion, not a premise. -/
lemma downwardAcceleration_formula
    (setup : WheelAndBlockSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hKinematics : SatisfiesConstantAccelerationKinematics setup) :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationReadout lengthUnit timeUnit setup.downwardAcceleration =
        2 *
          (lengthReadout lengthUnit setup.descentDistance -
            speedReadout lengthUnit timeUnit setup.initialDownwardSpeed *
              timeReadout timeUnit setup.elapsedTime) /
          (timeReadout timeUnit setup.elapsedTime) ^ 2 := by
  intro lengthUnit timeUnit
  have ht := hPhysical.elapsedTimePositive timeUnit
  have hk := hKinematics.descentEndpointEquation lengthUnit timeUnit
  field_simp
  nlinarith [sq_pos_of_pos ht]

/-- Eliminating the tension, angular acceleration, and disk moment of inertia
from the coupled laws gives `M = 2 m (g/a - 1)`.  This is the requested
physical relation, derived rather than assumed. -/
lemma wheelMass_formula
    (setup : WheelAndBlockSetup)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesUniformDiskInertiaLaw setup)
    (hDynamics : SatisfiesCoupledTranslationRotationDynamics setup) :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.wheelMass =
        2 * massReadout massUnit setup.suspendedObjectMass *
          (accelerationReadout lengthUnit timeUnit
                setup.gravitationalAcceleration /
              accelerationReadout lengthUnit timeUnit
                setup.downwardAcceleration -
            1) := by
  intro massUnit lengthUnit timeUnit
  let M := massReadout massUnit setup.wheelMass
  let m := massReadout massUnit setup.suspendedObjectMass
  let R := lengthReadout lengthUnit setup.wheelRadius
  let g :=
    accelerationReadout lengthUnit timeUnit setup.gravitationalAcceleration
  let a := accelerationReadout lengthUnit timeUnit setup.downwardAcceleration
  let T := forceReadout massUnit lengthUnit timeUnit setup.wireTension
  let I :=
    momentOfInertiaReadout massUnit lengthUnit setup.wheelMomentOfInertia
  let alpha :=
    angularAccelerationReadout timeUnit setup.wheelAngularAcceleration
  have hR : 0 < R := hPhysical.wheelRadiusPositive lengthUnit
  have ha : 0 < a :=
    hPhysical.downwardAccelerationPositive lengthUnit timeUnit
  have hI := hInertia.axialMomentOfInertia massUnit lengthUnit
  change I = (1 / 2 : ℝ) * M * R ^ 2 at hI
  have hN :=
    hDynamics.suspendedObjectNewtonSecondLaw massUnit lengthUnit timeUnit
  change m * g - T = m * a at hN
  have hRot :=
    hDynamics.wheelRotationalSecondLaw massUnit lengthUnit timeUnit
  change T * R = I * alpha at hRot
  have hC := hDynamics.noSlipTangentialCoupling lengthUnit timeUnit
  change a = R * alpha at hC
  have hTR : T = (1 / 2 : ℝ) * M * a := by
    apply mul_left_cancel₀ (ne_of_gt hR)
    calc
      R * T = T * R := mul_comm _ _
      _ = I * alpha := hRot
      _ = ((1 / 2 : ℝ) * M * R ^ 2) * alpha := by rw [hI]
      _ = R * ((1 / 2 : ℝ) * M * (R * alpha)) := by ring
      _ = R * ((1 / 2 : ℝ) * M * a) := by rw [← hC]
  change M = 2 * m * (g / a - 1)
  field_simp
  nlinarith

/-- Answer labels displayed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Wheel masses printed beside the answer choices, in kilograms. -/
def displayedWheelMassInKilograms : AnswerChoice → ℝ
  | .A => 42.3
  | .B => 46.5
  | .C => 41.9
  | .D => 58.0

/-- Dataset metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The modeled wheel mass is strictly closer to one displayed value than to
every other displayed value. -/
def IsUniqueClosestDisplayedWheelMass
    (setup : WheelAndBlockSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |massInKilograms setup.wheelMass -
        displayedWheelMassInKilograms choice| <
      |massInKilograms setup.wheelMass -
        displayedWheelMassInKilograms other|

/-!
The kinematic data give `a = 1.5 m/s²`.  The coupled translation/rotation
laws then give an exact modeled wheel mass of `46.48 kg`, whose one-decimal
multiple-choice value is uniquely closest to `46.5 kg`, answer `B`.

This is the formal target corresponding to
`thm:physics:phyx_mini_0771:target`.
-/
theorem problem_phyx_mini_0771
    (setup : WheelAndBlockSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hGravity : UsesStandardEarthGravity setup)
    (hNoSlip : UsesTautNoSlipUnwinding setup)
    (hPhysical : HasPhysicalParameters setup)
    (hInertia : SatisfiesUniformDiskInertiaLaw setup)
    (hDynamics : SatisfiesCoupledTranslationRotationDynamics setup)
    (hKinematics : SatisfiesConstantAccelerationKinematics setup) :
    accelerationInMetersPerSecondSquared setup.downwardAcceleration = 1.5 ∧
      massInKilograms setup.wheelMass = 46.48 ∧
      IsUniqueClosestDisplayedWheelMass setup .B := by
  have hAcceleration := downwardAcceleration_formula setup hPhysical hKinematics
      LengthUnit.meters TimeUnit.seconds
  have hDistance := hReadouts.descentDistanceMeters
  have hTime := hReadouts.elapsedTimeSeconds
  have hInitial :=
    hReadouts.releasedWithZeroSpeed LengthUnit.meters TimeUnit.seconds
  dsimp [lengthInMeters] at hDistance
  dsimp [timeInSeconds] at hTime
  norm_num [hDistance, hTime, hInitial] at hAcceleration
  have hAccelerationSI :
      accelerationInMetersPerSecondSquared
          setup.downwardAcceleration = 1.5 := by
    dsimp [accelerationInMetersPerSecondSquared]
    norm_num
    exact hAcceleration
  have hMass := wheelMass_formula setup hPhysical hInertia hDynamics
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hSuspended := hReadouts.suspendedMassKilograms
  dsimp [massInKilograms] at hSuspended
  have hGravitySI := hGravity.gravitationalAccelerationSI
  dsimp [accelerationInMetersPerSecondSquared] at hGravitySI
  norm_num [hSuspended, hGravitySI, hAcceleration] at hMass
  have hMassSI : massInKilograms setup.wheelMass = 46.48 := by
    dsimp [massInKilograms]
    norm_num
    exact hMass
  refine ⟨hAccelerationSI, hMassSI, ?_⟩
  intro other hOther
  rw [hMassSI]
  cases other with
  | A => norm_num [displayedWheelMassInKilograms]
  | B => exact (hOther rfl).elim
  | C => norm_num [displayedWheelMassInKilograms]
  | D => norm_num [displayedWheelMassInKilograms]

end PhyXMiniProblems.ProblemPhyXMini0771
