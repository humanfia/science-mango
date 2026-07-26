import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0785

open Dimension

/-!
# Tension exerted by a block on a flywheel

A `5.00 kg` block slides down a plane whose angle is printed as `36.9°`.
Kinetic friction has coefficient `0.25`.  A string parallel to the plane is
wrapped around a flywheel on the fixed axis labelled `O`; the flywheel has
mass `25.0 kg`, axial moment of inertia `0.500 kg m²`, and perpendicular
string lever arm `0.200 m`.

The physical magnitudes below use Physlib's unit-independent `Dimensionful`
representation.  Real numbers occur only as dimensionless data, coherent
unit readouts, and displayed answer values.  In particular, the requested
string tension and the two coupled accelerations are independent fields of
the setup, constrained only by the governing Newton--Euler and no-slip laws.
-/

/-! ## Dimensionful quantities and coherent unit readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative linear-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A scalar moment of inertia about the fixed axle, of dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- An angular-acceleration magnitude, with radians treated as dimensionless. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read force in coherent selected mass, length, and time units. -/
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

/-- Read angular acceleration in inverse square units of the selected time unit. -/
def angularAccelerationReadout
    (timeUnit : TimeUnit) (acceleration : AngularAccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- SI kilogram readout of a mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- SI metre readout of a length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- SI metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- SI newton readout of a force. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  forceReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds force

/-- SI kilogram-metre-squared readout of a moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters inertia

/-- Convert a dimensionless radian angle to degrees. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-! ## Scenario roles and primary-image geometry -/

/-- Direction along the inclined plane. -/
inductive AlongPlaneDirection where
  | downPlane
  | upPlane
  deriving DecidableEq, Repr

/-- The block's contact regime with the inclined surface. -/
inductive SurfaceContactRegime where
  | slidingWithKineticFriction
  | other
  deriving DecidableEq, Repr

/-- Idealization of the connecting string. -/
inductive StringModel where
  | lightInextensible
  | other
  deriving DecidableEq, Repr

/-- Contact between the wrapped string and the flywheel. -/
inductive StringFlywheelContact where
  | noSlip
  | slips
  deriving DecidableEq, Repr

/-- Constraint and resistance model at the flywheel axle. -/
inductive AxleModel where
  | fixedAtOWithNegligibleResistance
  | other
  deriving DecidableEq, Repr

/-- Physical objects visible in the supplied bitmap. -/
inductive FigureObject where
  | inclinedPlane
  | block
  | string
  | flywheel
  | fixedAxle
  deriving DecidableEq, Repr

/-- Labels printed in the supplied bitmap. -/
inductive FigureLabel where
  | blockMass
  | inclineAngle
  | axisO
  deriving DecidableEq, Repr

/-- A structured transcription of the primary figure. -/
structure SuppliedInclineFlywheelFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  labelRefersTo : FigureLabel → FigureObject
  blockMassLabelKilograms : ℝ
  inclineAngleLabelDegrees : ℝ
  blockLiesOnPlane : Bool
  blockIsDownhillOfFlywheel : Bool
  stringJoinsBlockToFlywheel : Bool
  stringRunsParallelToPlane : Bool
  stringWrapsAroundFlywheel : Bool
  axleOIsAtFlywheelCenter : Bool

/-!
The physical apparatus and its independent response quantities.  The
flywheel mass is retained even though its separately supplied axial inertia,
rather than a shape model, is what enters the rotational equation.
-/
structure InclineFlywheelSetup where
  blockMass : MassQuantity
  flywheelMass : MassQuantity
  flywheelMomentOfInertiaAboutO : MomentOfInertiaQuantity
  perpendicularStringLeverArm : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  normalForceOnBlock : ForceQuantity
  kineticFrictionForceOnBlock : ForceQuantity
  stringTension : ForceQuantity
  blockDownPlaneAcceleration : AccelerationQuantity
  flywheelAngularAcceleration : AngularAccelerationQuantity
  kineticFrictionCoefficient : ℝ
  inclineAngleRadians : ℝ
  blockMotionDirection : AlongPlaneDirection
  tensionDirectionOnBlock : AlongPlaneDirection
  frictionDirectionOnBlock : AlongPlaneDirection
  surfaceContactRegime : SurfaceContactRegime
  stringModel : StringModel
  stringFlywheelContact : StringFlywheelContact
  axleModel : AxleModel
  figure : SuppliedInclineFlywheelFigure

/-! ## Source data, figure readouts, and model calibrations -/

/-- Numerical and categorical data stated in the exercise prose. -/
structure MatchesProblemReadouts (setup : InclineFlywheelSetup) : Prop where
  blockMassKilograms : massInKilograms setup.blockMass = 5
  flywheelMassKilograms : massInKilograms setup.flywheelMass = 25
  flywheelInertiaKilogramMetersSquared :
    momentOfInertiaInKilogramMetersSquared
        setup.flywheelMomentOfInertiaAboutO = 1 / 2
  stringLeverArmMeters :
    lengthInMeters setup.perpendicularStringLeverArm = 1 / 5
  kineticFrictionCoefficientValue :
    setup.kineticFrictionCoefficient = 1 / 4
  blockSlidesDownPlane : setup.blockMotionDirection = .downPlane
  tensionActsUpPlane : setup.tensionDirectionOnBlock = .upPlane
  frictionActsUpPlane : setup.frictionDirectionOnBlock = .upPlane
  contactUsesKineticFriction :
    setup.surfaceContactRegime = .slidingWithKineticFriction
  stringIsLightAndInextensible : setup.stringModel = .lightInextensible
  stringDoesNotSlip : setup.stringFlywheelContact = .noSlip
  flywheelHasFixedAxleO :
    setup.axleModel = .fixedAtOWithNegligibleResistance

/-- Objects, labels, and incidences read from the primary image. -/
structure MatchesSuppliedFigure (setup : InclineFlywheelSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  blockMassLabelOnBlock :
    setup.figure.labelRefersTo .blockMass = .block
  inclineAngleLabelOnPlane :
    setup.figure.labelRefersTo .inclineAngle = .inclinedPlane
  axisOLabelOnAxle : setup.figure.labelRefersTo .axisO = .fixedAxle
  displayedBlockMass : setup.figure.blockMassLabelKilograms = 5
  displayedInclineAngle : setup.figure.inclineAngleLabelDegrees = 369 / 10
  displayedMassMatchesSetup :
    setup.figure.blockMassLabelKilograms = massInKilograms setup.blockMass
  blockOnPlane : setup.figure.blockLiesOnPlane = true
  blockDownhillOfFlywheel : setup.figure.blockIsDownhillOfFlywheel = true
  connectedString : setup.figure.stringJoinsBlockToFlywheel = true
  stringParallelToPlane : setup.figure.stringRunsParallelToPlane = true
  wrappedString : setup.figure.stringWrapsAroundFlywheel = true
  centralAxisO : setup.figure.axleOIsAtFlywheelCenter = true

/-- The printed degree label agrees with the physical angle to its displayed tenth. -/
def AngleRoundsToDisplayedTenth
    (angleRadians displayedDegrees : ℝ) : Prop :=
  |radiansToDegrees angleRadians - displayedDegrees| ≤ 1 / 20

/-!
The textbook numerical calibration implicit in the recorded choice: standard
near-Earth gravity and the `3-4-5` trigonometric components whose acute angle
rounds to the printed `36.9°`.  These are measurement/calibration readouts,
not assumptions about the requested tension.
-/
structure UsesTextbookGravityAndAngleCalibration
    (setup : InclineFlywheelSetup) : Prop where
  standardEarthGravity :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5
  inclineSine : Real.sin setup.inclineAngleRadians = 3 / 5
  inclineCosine : Real.cos setup.inclineAngleRadians = 4 / 5
  physicalAngleRoundsToFigureLabel :
    AngleRoundsToDisplayedTenth setup.inclineAngleRadians
      setup.figure.inclineAngleLabelDegrees

/-- Positivity and nondegeneracy selecting the stated downhill motion. -/
structure HasPhysicalParameters (setup : InclineFlywheelSetup) : Prop where
  blockMassPositive : ∀ massUnit,
    0 < massReadout massUnit setup.blockMass
  flywheelMassPositive : ∀ massUnit,
    0 < massReadout massUnit setup.flywheelMass
  inertiaPositive : ∀ massUnit lengthUnit,
    0 < momentOfInertiaReadout massUnit lengthUnit
      setup.flywheelMomentOfInertiaAboutO
  leverArmPositive : ∀ lengthUnit,
    0 < lengthReadout lengthUnit setup.perpendicularStringLeverArm
  gravityPositive : ∀ lengthUnit timeUnit,
    0 < accelerationReadout lengthUnit timeUnit
      setup.gravitationalAcceleration
  frictionCoefficientNonnegative : 0 ≤ setup.kineticFrictionCoefficient
  inclineAngleAcute : setup.inclineAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  positiveNetDownhillGravityComponent :
    0 < Real.sin setup.inclineAngleRadians -
      setup.kineticFrictionCoefficient * Real.cos setup.inclineAngleRadians

/-! ## Governing Newton--Euler and contact laws -/

/-!
The scalar laws use downhill as positive for the block and the corresponding
unwinding rotation as positive for the flywheel:

* normal balance: `N = m g cos θ`;
* kinetic friction: `fₖ = μₖ N`;
* translation: `m g sin θ - fₖ - T = m a`;
* rotation about `O`: `T r = I α`;
* no slip of the taut string: `a = r α`.

None of these laws states a numerical value for `T`.
-/
structure SatisfiesInclineFlywheelDynamics
    (setup : InclineFlywheelSetup) : Prop where
  normalBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit setup.normalForceOnBlock =
        massReadout massUnit setup.blockMass *
          accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            Real.cos setup.inclineAngleRadians
  coulombKineticFriction :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit
          setup.kineticFrictionForceOnBlock =
        setup.kineticFrictionCoefficient *
          forceReadout massUnit lengthUnit timeUnit setup.normalForceOnBlock
  blockNewtonSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.blockMass *
              accelerationReadout lengthUnit timeUnit
                setup.gravitationalAcceleration *
            Real.sin setup.inclineAngleRadians -
          forceReadout massUnit lengthUnit timeUnit
              setup.kineticFrictionForceOnBlock -
        forceReadout massUnit lengthUnit timeUnit setup.stringTension =
      massReadout massUnit setup.blockMass *
        accelerationReadout lengthUnit timeUnit
          setup.blockDownPlaneAcceleration
  flywheelRotationalSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit setup.stringTension *
          lengthReadout lengthUnit setup.perpendicularStringLeverArm =
        momentOfInertiaReadout massUnit lengthUnit
            setup.flywheelMomentOfInertiaAboutO *
          angularAccelerationReadout timeUnit
            setup.flywheelAngularAcceleration
  noSlipTangentialCoupling :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      accelerationReadout lengthUnit timeUnit
          setup.blockDownPlaneAcceleration =
        lengthReadout lengthUnit setup.perpendicularStringLeverArm *
          angularAccelerationReadout timeUnit
            setup.flywheelAngularAcceleration

/-!
Eliminating the normal force, kinetic friction, linear acceleration, and
angular acceleration gives the general tension formula.  This is a derived
relation, not a field or premise of the physical model.
-/
lemma stringTension_formula
    (setup : InclineFlywheelSetup)
    (_physical : HasPhysicalParameters setup)
    (_dynamics : SatisfiesInclineFlywheelDynamics setup) :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit setup.stringTension =
        momentOfInertiaReadout massUnit lengthUnit
              setup.flywheelMomentOfInertiaAboutO *
            massReadout massUnit setup.blockMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            (Real.sin setup.inclineAngleRadians -
              setup.kineticFrictionCoefficient *
                Real.cos setup.inclineAngleRadians) /
          (momentOfInertiaReadout massUnit lengthUnit
                setup.flywheelMomentOfInertiaAboutO +
            massReadout massUnit setup.blockMass *
              lengthReadout lengthUnit
                  setup.perpendicularStringLeverArm ^ 2) := by
  intro massUnit lengthUnit timeUnit
  have hm := _physical.blockMassPositive massUnit
  have hI := _physical.inertiaPositive massUnit lengthUnit
  have hnormal := _dynamics.normalBalance massUnit lengthUnit timeUnit
  have hfriction :=
    _dynamics.coulombKineticFriction massUnit lengthUnit timeUnit
  have htranslation :=
    _dynamics.blockNewtonSecondLaw massUnit lengthUnit timeUnit
  have hrotation :=
    _dynamics.flywheelRotationalSecondLaw massUnit lengthUnit timeUnit
  have hcoupling :=
    _dynamics.noSlipTangentialCoupling lengthUnit timeUnit
  rw [hfriction, hnormal] at htranslation
  have hInertiaAcceleration :
      momentOfInertiaReadout massUnit lengthUnit
            setup.flywheelMomentOfInertiaAboutO *
          accelerationReadout lengthUnit timeUnit
            setup.blockDownPlaneAcceleration =
        forceReadout massUnit lengthUnit timeUnit setup.stringTension *
          lengthReadout lengthUnit setup.perpendicularStringLeverArm ^ 2 := by
    calc
      momentOfInertiaReadout massUnit lengthUnit
              setup.flywheelMomentOfInertiaAboutO *
            accelerationReadout lengthUnit timeUnit
              setup.blockDownPlaneAcceleration =
          momentOfInertiaReadout massUnit lengthUnit
                setup.flywheelMomentOfInertiaAboutO *
              (lengthReadout lengthUnit setup.perpendicularStringLeverArm *
                angularAccelerationReadout timeUnit
                  setup.flywheelAngularAcceleration) := by
            rw [hcoupling]
      _ =
          (momentOfInertiaReadout massUnit lengthUnit
                setup.flywheelMomentOfInertiaAboutO *
              angularAccelerationReadout timeUnit
                setup.flywheelAngularAcceleration) *
            lengthReadout lengthUnit setup.perpendicularStringLeverArm := by
              ring
      _ =
          (forceReadout massUnit lengthUnit timeUnit setup.stringTension *
              lengthReadout lengthUnit setup.perpendicularStringLeverArm) *
            lengthReadout lengthUnit setup.perpendicularStringLeverArm := by
              rw [← hrotation]
      _ =
          forceReadout massUnit lengthUnit timeUnit setup.stringTension *
            lengthReadout lengthUnit setup.perpendicularStringLeverArm ^ 2 := by
              ring
  have hnetForce :
      forceReadout massUnit lengthUnit timeUnit setup.stringTension +
            massReadout massUnit setup.blockMass *
              accelerationReadout lengthUnit timeUnit
                setup.blockDownPlaneAcceleration =
        massReadout massUnit setup.blockMass *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration *
          (Real.sin setup.inclineAngleRadians -
            setup.kineticFrictionCoefficient *
              Real.cos setup.inclineAngleRadians) := by
    nlinarith [htranslation]
  have hdenominator :
      0 <
        momentOfInertiaReadout massUnit lengthUnit
              setup.flywheelMomentOfInertiaAboutO +
          massReadout massUnit setup.blockMass *
            lengthReadout lengthUnit
                setup.perpendicularStringLeverArm ^ 2 := by
    positivity
  apply (eq_div_iff (ne_of_gt hdenominator)).2
  calc
    forceReadout massUnit lengthUnit timeUnit setup.stringTension *
          (momentOfInertiaReadout massUnit lengthUnit
                setup.flywheelMomentOfInertiaAboutO +
            massReadout massUnit setup.blockMass *
              lengthReadout lengthUnit
                  setup.perpendicularStringLeverArm ^ 2) =
        momentOfInertiaReadout massUnit lengthUnit
              setup.flywheelMomentOfInertiaAboutO *
            forceReadout massUnit lengthUnit timeUnit setup.stringTension +
          massReadout massUnit setup.blockMass *
            (forceReadout massUnit lengthUnit timeUnit setup.stringTension *
              lengthReadout lengthUnit
                  setup.perpendicularStringLeverArm ^ 2) := by
            ring
    _ =
        momentOfInertiaReadout massUnit lengthUnit
              setup.flywheelMomentOfInertiaAboutO *
            forceReadout massUnit lengthUnit timeUnit setup.stringTension +
          massReadout massUnit setup.blockMass *
            (momentOfInertiaReadout massUnit lengthUnit
                setup.flywheelMomentOfInertiaAboutO *
              accelerationReadout lengthUnit timeUnit
                setup.blockDownPlaneAcceleration) := by
          rw [← hInertiaAcceleration]
    _ =
        momentOfInertiaReadout massUnit lengthUnit
              setup.flywheelMomentOfInertiaAboutO *
            (forceReadout massUnit lengthUnit timeUnit setup.stringTension +
              massReadout massUnit setup.blockMass *
                accelerationReadout lengthUnit timeUnit
                  setup.blockDownPlaneAcceleration) := by
          ring
    _ =
        momentOfInertiaReadout massUnit lengthUnit
              setup.flywheelMomentOfInertiaAboutO *
            (massReadout massUnit setup.blockMass *
              accelerationReadout lengthUnit timeUnit
                setup.gravitationalAcceleration *
              (Real.sin setup.inclineAngleRadians -
                setup.kineticFrictionCoefficient *
                  Real.cos setup.inclineAngleRadians)) := by
          rw [hnetForce]
    _ =
        momentOfInertiaReadout massUnit lengthUnit
              setup.flywheelMomentOfInertiaAboutO *
            massReadout massUnit setup.blockMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            (Real.sin setup.inclineAngleRadians -
              setup.kineticFrictionCoefficient *
                Real.cos setup.inclineAngleRadians) := by
          ring

/-! ## Multiple-choice presentation and formalization target -/

/-- Labels of the four tension choices printed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Tension in newtons printed beside each answer label. -/
def displayedTensionInNewtons : AnswerChoice → ℝ
  | .A => 108 / 10
  | .B => 14
  | .C => 158 / 10
  | .D => 21

/-- Dataset answer metadata, not used as a premise of the mechanics. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A displayed choice is uniquely closest to the modeled tension. -/
def IsUniqueClosestDisplayedTension
    (setup : InclineFlywheelSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |forceInNewtons setup.stringTension -
        displayedTensionInNewtons choice| <
      |forceInNewtons setup.stringTension -
        displayedTensionInNewtons other|

/-!
The governing laws and supplied numerical calibrations give `T = 14.0 N`,
so the uniquely closest displayed answer is B.

This formalizes blueprint label `thm:physics:phyx_mini_0785:target`.
-/
theorem problem_phyx_mini_0785
    (setup : InclineFlywheelSetup)
    (_readouts : MatchesProblemReadouts setup)
    (_figure : MatchesSuppliedFigure setup)
    (_calibration : UsesTextbookGravityAndAngleCalibration setup)
    (_physical : HasPhysicalParameters setup)
    (_dynamics : SatisfiesInclineFlywheelDynamics setup) :
    forceInNewtons setup.stringTension = displayedTensionInNewtons .B ∧
      IsUniqueClosestDisplayedTension setup .B ∧
      recordedDatasetAnswer = .B := by
  have hmass :
      massReadout MassUnit.kilograms setup.blockMass = 5 :=
    _readouts.blockMassKilograms
  have hinertia :
      momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters
          setup.flywheelMomentOfInertiaAboutO = 1 / 2 :=
    _readouts.flywheelInertiaKilogramMetersSquared
  have hradius :
      lengthReadout LengthUnit.meters setup.perpendicularStringLeverArm =
        1 / 5 :=
    _readouts.stringLeverArmMeters
  have hgravity :
      accelerationReadout LengthUnit.meters TimeUnit.seconds
          setup.gravitationalAcceleration = 49 / 5 :=
    _calibration.standardEarthGravity
  have htension :=
    stringTension_formula setup _physical _dynamics
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  rw [hinertia, hmass, hgravity, _calibration.inclineSine,
    _readouts.kineticFrictionCoefficientValue, _calibration.inclineCosine,
    hradius] at htension
  norm_num at htension
  have htensionNewtons : forceInNewtons setup.stringTension = 14 := by
    simpa [forceInNewtons] using htension
  constructor
  · simpa [displayedTensionInNewtons] using htensionNewtons
  constructor
  · intro other hother
    rw [htensionNewtons]
    cases other with
    | A => norm_num [displayedTensionInNewtons]
    | B => exact (hother rfl).elim
    | C => norm_num [displayedTensionInNewtons]
    | D => norm_num [displayedTensionInNewtons]
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0785
