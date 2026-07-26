import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.RigidBody.KineticEnergy
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0774

open Dimension

/-!
# Speed in a two-block system with a massive pulley

The primary image shows a `4.00 kg` block on the left and a `2.00 kg` block
on the right, joined by a rope over a fixed pulley.  The left block is `5.00 m`
above the floor.  The problem gives pulley radius `0.160 m`, axial moment of
inertia `0.380 kg m²`, and states that the rope does not slip on the rim.

Masses, lengths, speeds, accelerations, angular speeds, moment of inertia, and
energy retain their physical dimensions through Physlib's unit-independent
`Dimensionful` quantities.  Real numbers occur only in coherent-SI readouts,
schematic figure data, and displayed answer values.  In particular, the impact
speed is an independent physical field and is not defined from answer B.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The dimension `L T⁻²` of an acceleration magnitude. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The dimension `T⁻¹` of angular speed; radians are dimensionless. -/
def angularSpeedDimension : Dimension := T𝓭⁻¹

/-- The dimension `M L²` of a scalar moment of inertia about an axis. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent block mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative angular-speed magnitude. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative axial moment of inertia. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A unit-independent physical energy. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical speed in coherent-SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Read an acceleration in coherent-SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read angular speed in radians per coherent-SI second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed UnitChoices.SI).val : ℝ)

/-- Read an axial moment of inertia in coherent-SI `kg m²`. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a physical energy in joules, calibrated by Physlib's joule. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Physical roles and primary-image vocabulary -/

/-- The two blocks, named by their positions and printed mass labels. -/
inductive BlockLabel where
  | leftFourKilogram
  | rightTwoKilogram
  deriving DecidableEq, Fintype, Repr

/-- Left/right placement in the supplied diagram. -/
inductive FigureSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Initial support relation visible in the supplied diagram. -/
inductive InitialPlacement where
  | suspendedAboveFloor
  | restingAtFloor
  deriving DecidableEq, Repr

/-- Vertical directions indicated by the intended motion. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Physical and graphical objects visible in image `774.png`. -/
inductive FigureObject where
  | ceilingSupport
  | fixedPulley
  | rope
  | leftBlock
  | rightBlock
  | fiveMeterDistanceArrow
  deriving DecidableEq, Fintype, Repr

/-- How the pulley axle is mounted. -/
inductive PulleyMounting where
  | fixedToCeiling
  deriving DecidableEq, Repr

/-- Idealization of the connecting rope used by the textbook model. -/
inductive RopeModel where
  | masslessInextensible
  deriving DecidableEq, Repr

/-- Contact condition between the rope and the pulley rim. -/
inductive RopePulleyContact where
  | noSlip
  deriving DecidableEq, Repr

/-- Dissipation model at the fixed axle. -/
inductive AxleModel where
  | frictionless
  deriving DecidableEq, Repr

/-- Initial state needed by the recorded energy calculation. -/
inductive ReleaseState where
  | releasedFromRest
  deriving DecidableEq, Repr

/-- The event at which the requested speed is measured. -/
inductive MeasurementEvent where
  | leftBlockJustBeforeFloorImpact
  deriving DecidableEq, Repr

/-!
Literal qualitative and numerical information transcribed from the primary
bitmap.  The ordering data describe the drawing; they are not physical scalar
coordinates.
-/
structure MassivePulleyFigure where
  showsObject : FigureObject → Bool
  sideOfBlock : BlockLabel → FigureSide
  initialPlacement : BlockLabel → InitialPlacement
  printedMassKilograms : BlockLabel → ℝ
  printedDistanceMeters : ℝ
  distanceArrowAssociatedBlock : BlockLabel
  indicatedMotionDirection : BlockLabel → VerticalDirection
  pulleyDrawnAboveBothBlocks : Bool
  ropeConnectsBlocksOverPulley : Bool

/-!
Independent physical quantities and qualitative model choices.  The scalar
impact speed and angular speed are fields rather than definitions made from
the recorded answer or from the target closed form.
-/
structure MassivePulleyAtwoodSetup where
  figure : MassivePulleyFigure
  blockMass : BlockLabel → MassQuantity
  descentDistance : LengthQuantity
  pulleyRadius : LengthQuantity
  pulleyMomentOfInertia : MomentOfInertiaQuantity
  gravitationalAcceleration : AccelerationQuantity
  impactSpeed : SpeedQuantity
  impactAngularSpeed : AngularSpeedQuantity
  pulleyRotationalEnergyAtImpact : EnergyQuantity
  pulleyRigidBodySI : RigidBody 3
  pulleyAxis : Fin 3
  angularVelocityVectorAtImpact : Fin 3 → ℝ
  pulleyMounting : PulleyMounting
  ropeModel : RopeModel
  ropePulleyContact : RopePulleyContact
  axleModel : AxleModel
  initialState : ReleaseState
  measurementEvent : MeasurementEvent
  blockMotionDirection : BlockLabel → VerticalDirection

/-! ## Figure evidence, problem data, textbook assumptions, and laws -/

/-- Geometry and labels read directly from the primary image. -/
structure MatchesPrimaryFigure (setup : MassivePulleyAtwoodSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  fourKilogramBlockOnLeft :
    setup.figure.sideOfBlock .leftFourKilogram = .left
  twoKilogramBlockOnRight :
    setup.figure.sideOfBlock .rightTwoKilogram = .right
  leftBlockInitiallySuspended :
    setup.figure.initialPlacement .leftFourKilogram = .suspendedAboveFloor
  rightBlockInitiallyAtFloor :
    setup.figure.initialPlacement .rightTwoKilogram = .restingAtFloor
  leftPrintedMass :
    setup.figure.printedMassKilograms .leftFourKilogram = 4
  rightPrintedMass :
    setup.figure.printedMassKilograms .rightTwoKilogram = 2
  physicalMassesMatchPrintedLabels :
    ∀ block,
      massInKilograms (setup.blockMass block) =
        setup.figure.printedMassKilograms block
  printedVerticalDistance : setup.figure.printedDistanceMeters = 5
  physicalDescentMatchesPrintedDistance :
    lengthInMeters setup.descentDistance =
      setup.figure.printedDistanceMeters
  distanceArrowBelongsToLeftBlock :
    setup.figure.distanceArrowAssociatedBlock = .leftFourKilogram
  figureIndicatesLeftBlockDownward :
    setup.figure.indicatedMotionDirection .leftFourKilogram = .downward
  pulleyIsAboveBlocks : setup.figure.pulleyDrawnAboveBothBlocks = true
  ropeRouteShown : setup.figure.ropeConnectsBlocksOverPulley = true

/-!
The numerical pulley data and no-slip statement from the prose.  No impact
speed or answer-choice value occurs in these premises.
-/
structure MatchesProblemStatement
    (setup : MassivePulleyAtwoodSetup) : Prop where
  pulleyFixedToCeiling : setup.pulleyMounting = .fixedToCeiling
  radiusMeters : lengthInMeters setup.pulleyRadius = 4 / 25
  momentOfInertiaKilogramMetersSquared :
    momentOfInertiaInKilogramMetersSquared
        setup.pulleyMomentOfInertia = 19 / 50
  ropeDoesNotSlip : setup.ropePulleyContact = .noSlip

/-!
Additional idealizations needed by the textbook answer but not stated
explicitly in the short prompt: release from rest, a massless inextensible
rope, and no dissipative axle friction.
-/
structure UsesIdealTextbookReleaseModel
    (setup : MassivePulleyAtwoodSetup) : Prop where
  initiallyReleasedFromRest : setup.initialState = .releasedFromRest
  ropeIsMasslessAndInextensible : setup.ropeModel = .masslessInextensible
  axleHasNoDissipativeFriction : setup.axleModel = .frictionless
  requestedMeasurementEvent :
    setup.measurementEvent = .leftBlockJustBeforeFloorImpact
  leftBlockDescends :
    setup.blockMotionDirection .leftFourKilogram = .downward
  rightBlockRises :
    setup.blockMotionDirection .rightTwoKilogram = .upward

/-- Standard near-Earth gravitational calibration used by the recorded answer. -/
structure UsesStandardNearEarthGravity
    (setup : MassivePulleyAtwoodSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 49 / 5

/-- Positivity and mass ordering selecting the depicted physical branch. -/
structure HasPhysicalParameters
    (setup : MassivePulleyAtwoodSetup) : Prop where
  everyBlockMassPositive :
    ∀ block, 0 < massInKilograms (setup.blockMass block)
  leftBlockIsHeavier :
    massInKilograms (setup.blockMass .rightTwoKilogram) <
      massInKilograms (setup.blockMass .leftFourKilogram)
  descentDistancePositive : 0 < lengthInMeters setup.descentDistance
  pulleyRadiusPositive : 0 < lengthInMeters setup.pulleyRadius
  pulleyInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.pulleyMomentOfInertia
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  impactSpeedPositive : 0 < speedInMetersPerSecond setup.impactSpeed
  impactAngularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond setup.impactAngularSpeed

/-!
Governing laws for the ideal massive-pulley Atwood model.

* No slip equates the rope speed to radius times angular speed.
* The pulley inertia is the tensor entry about its fixed axis, and its angular
  velocity points along that axis.
* Pulley rotational energy is Physlib's
  `RigidBody.rotationalKineticEnergy`.
* Conservation of energy equates the net gravitational potential-energy loss
  to the two blocks' translational kinetic energy plus the pulley's rotational
  kinetic energy.

These laws mention neither `6272 / 667` nor `3.07 m/s`.
-/
structure SatisfiesMassivePulleyEnergyLaws
    (setup : MassivePulleyAtwoodSetup) : Prop where
  noSlipKinematics :
    speedInMetersPerSecond setup.impactSpeed =
      lengthInMeters setup.pulleyRadius *
        angularSpeedInRadiansPerSecond setup.impactAngularSpeed
  axialTensorEntryMatchesScalarInertia :
    setup.pulleyRigidBodySI.inertiaTensor
        setup.pulleyAxis setup.pulleyAxis =
      momentOfInertiaInKilogramMetersSquared
        setup.pulleyMomentOfInertia
  angularVelocityIsAlongPulleyAxis :
    ∀ component : Fin 3,
      setup.angularVelocityVectorAtImpact component =
        if component = setup.pulleyAxis then
          angularSpeedInRadiansPerSecond setup.impactAngularSpeed
        else 0
  rotationalEnergyUsesPhyslib :
    energyInJoules setup.pulleyRotationalEnergyAtImpact =
      setup.pulleyRigidBodySI.rotationalKineticEnergy
        setup.angularVelocityVectorAtImpact
  mechanicalEnergyConservation :
    (massInKilograms (setup.blockMass .leftFourKilogram) -
          massInKilograms (setup.blockMass .rightTwoKilogram)) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        lengthInMeters setup.descentDistance =
      (1 / 2 : ℝ) *
          (massInKilograms (setup.blockMass .leftFourKilogram) +
            massInKilograms (setup.blockMass .rightTwoKilogram)) *
          speedInMetersPerSecond setup.impactSpeed ^ 2 +
        energyInJoules setup.pulleyRotationalEnergyAtImpact

/-! ## Derived physical relations and answer metadata -/

/-!
The tensor contraction reduces to the scalar pulley relation
`K_rot = I * omega² / 2` because angular velocity lies along the fixed axis.
-/
lemma pulleyRotationalEnergy_eq_half_inertia_mul_angularSpeed_sq
    (setup : MassivePulleyAtwoodSetup)
    (_laws : SatisfiesMassivePulleyEnergyLaws setup) :
    energyInJoules setup.pulleyRotationalEnergyAtImpact =
      (1 / 2 : ℝ) *
        momentOfInertiaInKilogramMetersSquared
          setup.pulleyMomentOfInertia *
        angularSpeedInRadiansPerSecond setup.impactAngularSpeed ^ 2 := by
  rw [_laws.rotationalEnergyUsesPhyslib]
  have hω :
      setup.angularVelocityVectorAtImpact =
        Pi.single setup.pulleyAxis
          (angularSpeedInRadiansPerSecond setup.impactAngularSpeed) := by
    funext component
    simpa [Pi.single_apply, eq_comm] using
      _laws.angularVelocityIsAlongPulleyAxis component
  rw [hω, RigidBody.rotationalKineticEnergy]
  rw [Matrix.mulVec_single, single_dotProduct]
  simp [_laws.axialTensorEntryMatchesScalarInertia]
  ring

/-!
Substitution of the figure, pulley, gravity, no-slip, and energy data gives the
exact squared impact speed `6272 / 667 (m/s)²`.
-/
lemma impactSpeed_squared_eq_6272_over_667
    (setup : MassivePulleyAtwoodSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_statement : MatchesProblemStatement setup)
    (_model : UsesIdealTextbookReleaseModel setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesMassivePulleyEnergyLaws setup) :
    speedInMetersPerSecond setup.impactSpeed ^ 2 = 6272 / 667 := by
  have hleft :
      massInKilograms (setup.blockMass .leftFourKilogram) = 4 :=
    (_figure.physicalMassesMatchPrintedLabels .leftFourKilogram).trans
      _figure.leftPrintedMass
  have hright :
      massInKilograms (setup.blockMass .rightTwoKilogram) = 2 :=
    (_figure.physicalMassesMatchPrintedLabels .rightTwoKilogram).trans
      _figure.rightPrintedMass
  have hdistance : lengthInMeters setup.descentDistance = 5 :=
    _figure.physicalDescentMatchesPrintedDistance.trans
      _figure.printedVerticalDistance
  have henergy := _laws.mechanicalEnergyConservation
  rw [hleft, hright, _gravity.gravityMetersPerSecondSquared, hdistance,
    pulleyRotationalEnergy_eq_half_inertia_mul_angularSpeed_sq setup _laws,
    _statement.momentOfInertiaKilogramMetersSquared] at henergy
  have hnoSlip := _laws.noSlipKinematics
  rw [_statement.radiusMeters] at hnoSlip
  have hnoSlipSq := congrArg (fun x : ℝ => x ^ 2) hnoSlip
  nlinarith [hnoSlipSq, sq_nonneg
    (angularSpeedInRadiansPerSecond setup.impactAngularSpeed)]

/-- The positive physical branch of the exact impact-speed solution. -/
lemma impactSpeed_eq_sqrt_6272_over_667
    (setup : MassivePulleyAtwoodSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_statement : MatchesProblemStatement setup)
    (_model : UsesIdealTextbookReleaseModel setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesMassivePulleyEnergyLaws setup) :
    speedInMetersPerSecond setup.impactSpeed =
      Real.sqrt (6272 / 667) := by
  have hvSq :=
    impactSpeed_squared_eq_6272_over_667 setup _figure _statement
      _model _gravity _physical _laws
  have hratio : (0 : ℝ) ≤ 6272 / 667 := by norm_num
  have hsqrtSq := Real.sq_sqrt hratio
  have hsqrtNonneg := Real.sqrt_nonneg (6272 / 667 : ℝ)
  nlinarith [_physical.impactSpeedPositive]

/-- Labels of the four speed choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre-per-second value printed beside each answer label. -/
def AnswerChoice.displayedSpeedMetersPerSecond : AnswerChoice → ℝ
  | .A => 89 / 25
  | .B => 307 / 100
  | .C => 407 / 100
  | .D => 114 / 25

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A computed speed matches a two-decimal answer when it lies in that displayed
hundredth's half-open rounding interval.
-/
def RoundsToDisplayedSpeed
    (setup : MassivePulleyAtwoodSetup) (choice : AnswerChoice) : Prop :=
  choice.displayedSpeedMetersPerSecond - 1 / 200 ≤
      speedInMetersPerSecond setup.impactSpeed ∧
    speedInMetersPerSecond setup.impactSpeed <
      choice.displayedSpeedMetersPerSecond + 1 / 200

/-- A choice is the unique displayed speed to which the impact speed rounds. -/
def IsUniqueRoundedAnswer
    (setup : MassivePulleyAtwoodSetup) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedSpeed setup choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedSpeed setup other → other = choice

/-!
The exact impact speed is `sqrt (6272 / 667) m/s`, approximately
`3.06648 m/s`, so it rounds uniquely to `3.07 m/s`, answer choice B.

This formalizes blueprint label `thm:physics:phyx_mini_0774:target`.
-/
theorem problem_phyx_mini_0774
    (setup : MassivePulleyAtwoodSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_statement : MatchesProblemStatement setup)
    (_model : UsesIdealTextbookReleaseModel setup)
    (_gravity : UsesStandardNearEarthGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesMassivePulleyEnergyLaws setup) :
    speedInMetersPerSecond setup.impactSpeed =
        Real.sqrt (6272 / 667) ∧
      IsUniqueRoundedAnswer setup .B := by
  have hv :=
    impactSpeed_eq_sqrt_6272_over_667 setup _figure _statement
      _model _gravity _physical _laws
  refine ⟨hv, ?_⟩
  have hratio : (0 : ℝ) ≤ 6272 / 667 := by norm_num
  have hroundB : RoundsToDisplayedSpeed setup .B := by
    constructor
    · change (307 / 100 : ℝ) - 1 / 200 ≤
        speedInMetersPerSecond setup.impactSpeed
      rw [hv]
      rw [Real.le_sqrt (by norm_num) hratio]
      norm_num
    · change speedInMetersPerSecond setup.impactSpeed <
        (307 / 100 : ℝ) + 1 / 200
      rw [hv]
      rw [Real.sqrt_lt hratio (by norm_num)]
      norm_num
  refine ⟨hroundB, ?_⟩
  intro other hother
  fin_cases other
  · exfalso
    have hOtherLower := hother.1
    have hBUpper := hroundB.2
    norm_num [RoundsToDisplayedSpeed,
      AnswerChoice.displayedSpeedMetersPerSecond] at hOtherLower hBUpper
    linarith
  · rfl
  · exfalso
    have hOtherLower := hother.1
    have hBUpper := hroundB.2
    norm_num [RoundsToDisplayedSpeed,
      AnswerChoice.displayedSpeedMetersPerSecond] at hOtherLower hBUpper
    linarith
  · exfalso
    have hOtherLower := hother.1
    have hBUpper := hroundB.2
    norm_num [RoundsToDisplayedSpeed,
      AnswerChoice.displayedSpeedMetersPerSecond] at hOtherLower hBUpper
    linarith

end PhyXMiniProblems.ProblemPhyXMini0774
