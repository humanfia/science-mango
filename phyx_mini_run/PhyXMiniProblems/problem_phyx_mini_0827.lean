import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Bullet embedding in a freely hinged door

A uniform door of width `1.00 m` and mass `15 kg` is initially at rest and
rotates freely about the vertical axis through its hinges.  A `10 g` bullet
travelling at `400 m/s` perpendicular to the door strikes its centre,
`0.50 m` from the hinge axis, and embeds in the door.

The primary bitmap distinguishes the full door width `d = 1.00 m` from the
hinge-to-impact distance `ℓ = 0.50 m`.  This resolves the auxiliary caption's
interchange of the two labels.

Masses, lengths, speed, angular speed, moments of inertia, and angular
momenta are represented by unit-independent Physlib quantities.  Real
numbers occur only as coherent unit readouts and displayed answer data.

Assumption/target split:

* governing laws: centre-impact geometry, the uniform-door and point-mass
  inertia formulas, negligible external angular impulse about the hinge axis,
  the `I * omega` angular-momentum relations, and conservation of angular
  momentum during the embedding collision;
* previous-part results: none;
* data and figure readouts: `M = 15 kg`, `m = 10 g`, `d = 1.00 m`,
  `ℓ = 0.50 m`, `v_bullet = 400 m/s`, the perpendicular incoming arrow,
  the upper hinge, and the embedded bullet and `omega` arrow after impact;
* current targets: the exact SI angular-speed readout `800 / 2001 rad/s`, its
  rounding to `0.40 rad/s`, and agreement with recorded answer choice B.
  These claims occur only in lemma and theorem conclusions.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0827

open Dimension

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- The physical dimension `mass * length^2` of an axial moment of inertia. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- The physical dimension `mass * length^2 / time` of angular momentum. -/
def angularMomentumDimension : Dimension :=
  momentOfInertiaDimension * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative scalar moment of inertia about the hinge axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A nonnegative angular-momentum magnitude about the hinge axis. -/
abbrev AngularMomentumQuantity : Type :=
  Dimensionful (WithDim angularMomentumDimension NNReal)

/-- Read a mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read angular speed in inverse units of the selected time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read moment of inertia in coherent selected mass and length units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Read angular momentum in coherent selected mechanical units. -/
def angularMomentumReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (angularMomentum : AngularMomentumQuantity) : ℝ :=
  ((angularMomentum {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Gram readout used for the bullet-mass label. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metres-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Radians-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  angularSpeedReadout TimeUnit.seconds angularSpeed

/-- Kilogram-metre-squared readout of a moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters inertia

/-- Kilogram-metre-squared-per-second readout of angular momentum. -/
def angularMomentumInKilogramMetersSquaredPerSecond
    (angularMomentum : AngularMomentumQuantity) : ℝ :=
  angularMomentumReadout
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds angularMomentum

/-! ## Physical roles and primary-image vocabulary -/

/-- Configurations explicitly labelled `Before` and `After` in image `827.png`. -/
inductive CollisionStage where
  | before
  | after
  deriving DecidableEq, Fintype, Repr

/-- Physical or graphical objects visibly distinguished in the primary image. -/
inductive FigureObject where
  | door
  | bullet
  | hinge
  | bulletVelocityArrow
  | angularVelocityArrow
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic and stage labels visible in the primary image. -/
inductive FigureLabel where
  | doorMassM
  | bulletMassm
  | doorWidthd
  | hingeToImpactDistanceEll
  | bulletSpeedV
  | finalAngularSpeedOmega
  | beforeStage
  | afterStage
  deriving DecidableEq, Fintype, Repr

/-- The physical axis about which the door is allowed to rotate. -/
inductive DoorRotationAxis where
  | verticalThroughHinges
  | other
  deriving DecidableEq, Repr

/-- Direction of the incident bullet relative to the plane of the door. -/
inductive IncidenceDirection where
  | perpendicularToDoorPlane
  | obliqueToDoorPlane
  | parallelToDoorPlane
  deriving DecidableEq, Repr

/-- Idealized mass distribution used by the standard door-inertia law. -/
inductive DoorModel where
  | uniformRectangularDoor
  | other
  deriving DecidableEq, Repr

/-- Qualitative outcome of the short bullet-door collision. -/
inductive CollisionOutcome where
  | bulletEmbeddedInDoor
  | bulletRebounds
  | bulletPassesThrough
  deriving DecidableEq, Repr

/-- Direction in which the after-impact door is drawn relative to `Before`. -/
inductive DepictedRotationSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-!
Typed evidence transcribed from the primary bitmap.  In particular, the
independent fields for `d` and `ℓ` preserve the image's full-width and
hinge-to-centre roles rather than following the swapped auxiliary caption.
-/
structure DoorImpactFigure where
  showsObject : CollisionStage → FigureObject → Bool
  showsLabel : FigureLabel → Bool
  depictedDoorMass : MassQuantity
  depictedBulletMass : MassQuantity
  depictedDoorWidth_d : LengthQuantity
  depictedHingeToImpactDistance_ell : LengthQuantity
  depictedBulletSpeed : SpeedQuantity
  depictedFinalAngularSpeed : AngularSpeedQuantity
  doorInitiallyVerticalOnPage : Bool
  widthArrowSpansHingeToFarEdge : Bool
  impactDistanceArrowSpansHingeToBulletPath : Bool
  bulletPathMeetsDoorAtCenter : Bool
  bulletArrowPerpendicularToDoor : Bool
  bulletShownEmbeddedAfterImpact : Bool
  afterRotationSense : DepictedRotationSense

/-!
Independent physical quantities for the collision.  The requested final
angular speed is stored independently and is constrained only by the laws
below; it is not defined to be an answer choice.
-/
structure DoorBulletSetup where
  doorMass : MassQuantity
  bulletMass : MassQuantity
  doorWidth : LengthQuantity
  hingeToImpactDistance : LengthQuantity
  bulletInitialSpeed : SpeedQuantity
  doorInitialAngularSpeed : AngularSpeedQuantity
  finalAngularSpeed : AngularSpeedQuantity
  doorMomentOfInertiaAboutHinge : MomentOfInertiaQuantity
  embeddedBulletMomentOfInertiaAboutHinge : MomentOfInertiaQuantity
  combinedMomentOfInertiaAfterImpact : MomentOfInertiaQuantity
  initialAngularMomentumAboutHinge : AngularMomentumQuantity
  finalAngularMomentumAboutHinge : AngularMomentumQuantity
  rotationAxis : DoorRotationAxis
  incidenceDirection : IncidenceDirection
  doorModel : DoorModel
  collisionOutcome : CollisionOutcome
  rotatesFreelyAboutHinges : Bool
  bulletAndDoorCorotateAfterImpact : Bool
  hingeImpulseActsThroughRotationAxis : Bool
  externalAngularImpulseAboutHingeNegligible : Bool
  figure : DoorImpactFigure

/-! ## Scenario, data, and figure readouts -/

/-- Qualitative apparatus and collision assumptions stated in the problem. -/
structure MatchesDoorBulletScenario (setup : DoorBulletSetup) : Prop where
  verticalHingeAxis : setup.rotationAxis = .verticalThroughHinges
  freelyRotatingDoor : setup.rotatesFreelyAboutHinges = true
  uniformDoorModel : setup.doorModel = .uniformRectangularDoor
  perpendicularIncidence :
    setup.incidenceDirection = .perpendicularToDoorPlane
  bulletEmbeds : setup.collisionOutcome = .bulletEmbeddedInDoor
  embeddedBulletCorotates : setup.bulletAndDoorCorotateAfterImpact = true

/-- The values printed in the problem and primary image. -/
structure MatchesProblemReadouts (setup : DoorBulletSetup) : Prop where
  doorMassKilograms : massInKilograms setup.doorMass = 15
  bulletMassGrams : massInGrams setup.bulletMass = 10
  bulletMassKilograms : massInKilograms setup.bulletMass = 1 / 100
  doorWidthMeters : lengthInMeters setup.doorWidth = 1
  hingeToImpactDistanceMeters :
    lengthInMeters setup.hingeToImpactDistance = 1 / 2
  bulletSpeedMetersPerSecond :
    speedInMetersPerSecond setup.bulletInitialSpeed = 400

/-- Direct object, label, and spatial evidence from image `827.png`. -/
structure MatchesPrimaryDoorImpactFigure (setup : DoorBulletSetup) : Prop where
  beforeDoorShown : setup.figure.showsObject .before .door = true
  beforeBulletShown : setup.figure.showsObject .before .bullet = true
  beforeHingeShown : setup.figure.showsObject .before .hinge = true
  incomingVelocityArrowShown :
    setup.figure.showsObject .before .bulletVelocityArrow = true
  afterDoorShown : setup.figure.showsObject .after .door = true
  embeddedBulletShown : setup.figure.showsObject .after .bullet = true
  afterHingeShown : setup.figure.showsObject .after .hinge = true
  angularVelocityArrowShown :
    setup.figure.showsObject .after .angularVelocityArrow = true
  everyPrintedLabelShown : ∀ label, setup.figure.showsLabel label = true
  labelMDenotesDoorMass : setup.figure.depictedDoorMass = setup.doorMass
  labelmDenotesBulletMass : setup.figure.depictedBulletMass = setup.bulletMass
  labeldDenotesDoorWidth :
    setup.figure.depictedDoorWidth_d = setup.doorWidth
  labelEllDenotesHingeToImpactDistance :
    setup.figure.depictedHingeToImpactDistance_ell =
      setup.hingeToImpactDistance
  labelVDenotesBulletSpeed :
    setup.figure.depictedBulletSpeed = setup.bulletInitialSpeed
  labelOmegaDenotesFinalAngularSpeed :
    setup.figure.depictedFinalAngularSpeed = setup.finalAngularSpeed
  initialDoorDrawnVertical : setup.figure.doorInitiallyVerticalOnPage = true
  widthArrowHasFullDoorExtent :
    setup.figure.widthArrowSpansHingeToFarEdge = true
  ellArrowEndsAtBulletPath :
    setup.figure.impactDistanceArrowSpansHingeToBulletPath = true
  pathIntersectsDoorAtCenter :
    setup.figure.bulletPathMeetsDoorAtCenter = true
  bulletArrowNormalToDoor :
    setup.figure.bulletArrowPerpendicularToDoor = true
  bulletEmbeddedInAfterPanel :
    setup.figure.bulletShownEmbeddedAfterImpact = true
  afterPanelTurnsClockwise :
    setup.figure.afterRotationSense = .clockwise

/-- Rest condition and hinge-impulse facts for the short collision interval. -/
structure MatchesCollisionBoundaryConditions
    (setup : DoorBulletSetup) : Prop where
  doorInitiallyAtRest :
    ∀ timeUnit : TimeUnit,
      angularSpeedReadout timeUnit setup.doorInitialAngularSpeed = 0
  hingeImpulseThroughAxis :
    setup.hingeImpulseActsThroughRotationAxis = true
  negligibleExternalAngularImpulse :
    setup.externalAngularImpulseAboutHingeNegligible = true

/-- Positivity selecting the nondegenerate physical branch. -/
structure HasPhysicalDoorBulletParameters (setup : DoorBulletSetup) : Prop where
  positiveDoorMass : 0 < massInKilograms setup.doorMass
  positiveBulletMass : 0 < massInKilograms setup.bulletMass
  positiveDoorWidth : 0 < lengthInMeters setup.doorWidth
  positiveImpactDistance : 0 < lengthInMeters setup.hingeToImpactDistance
  positiveBulletSpeed : 0 < speedInMetersPerSecond setup.bulletInitialSpeed
  positiveDoorInertia :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.doorMomentOfInertiaAboutHinge
  positiveEmbeddedBulletInertia :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.embeddedBulletMomentOfInertiaAboutHinge
  positiveCombinedInertia :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.combinedMomentOfInertiaAfterImpact

/-! ## Governing geometry, inertia, and angular-momentum laws -/

/-!
The bullet strikes the door's centre, so its lever arm about the hinge axis is
half the door width.  This is a geometric law and does not mention `omega`.
-/
structure SatisfiesCenterImpactGeometry (setup : DoorBulletSetup) : Prop where
  impactAtDoorCenter :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit setup.hingeToImpactDistance =
        lengthReadout lengthUnit setup.doorWidth / 2

/-!
The uniform door has edge-axis inertia `(1/3) M d^2`; the embedded bullet is
a point mass with inertia `m ℓ^2`; the after-impact inertia is their sum.
These shape laws leave the requested angular speed unconstrained.
-/
structure SatisfiesDoorBulletInertiaLaws (setup : DoorBulletSetup) : Prop where
  uniformDoorAboutHinges :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.doorMomentOfInertiaAboutHinge =
        (1 / 3 : ℝ) * massReadout massUnit setup.doorMass *
          lengthReadout lengthUnit setup.doorWidth ^ 2
  embeddedBulletAsPointMass :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.embeddedBulletMomentOfInertiaAboutHinge =
        massReadout massUnit setup.bulletMass *
          lengthReadout lengthUnit setup.hingeToImpactDistance ^ 2
  combinedInertiaIsSum :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.combinedMomentOfInertiaAfterImpact =
        momentOfInertiaReadout massUnit lengthUnit
            setup.doorMomentOfInertiaAboutHinge +
          momentOfInertiaReadout massUnit lengthUnit
            setup.embeddedBulletMomentOfInertiaAboutHinge

/-!
Angular momentum about the hinge axis during the short, perfectly inelastic
impact.  Perpendicular incidence makes the bullet term `m v ℓ`; the initially
stationary door term is retained in the general balance and separately set to
zero by the boundary conditions.  The final embedded assembly has angular
momentum `I_total * omega`.
-/
structure SatisfiesAngularMomentumConservationAtImpact
    (setup : DoorBulletSetup) : Prop where
  externalAngularImpulseNegligible :
    setup.externalAngularImpulseAboutHingeNegligible = true
  initialAngularMomentumLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      angularMomentumReadout massUnit lengthUnit timeUnit
          setup.initialAngularMomentumAboutHinge =
        massReadout massUnit setup.bulletMass *
            speedReadout lengthUnit timeUnit setup.bulletInitialSpeed *
            lengthReadout lengthUnit setup.hingeToImpactDistance +
          momentOfInertiaReadout massUnit lengthUnit
              setup.doorMomentOfInertiaAboutHinge *
            angularSpeedReadout timeUnit setup.doorInitialAngularSpeed
  finalAngularMomentumLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      angularMomentumReadout massUnit lengthUnit timeUnit
          setup.finalAngularMomentumAboutHinge =
        momentOfInertiaReadout massUnit lengthUnit
            setup.combinedMomentOfInertiaAfterImpact *
          angularSpeedReadout timeUnit setup.finalAngularSpeed
  angularMomentumConserved :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      angularMomentumReadout massUnit lengthUnit timeUnit
          setup.initialAngularMomentumAboutHinge =
        angularMomentumReadout massUnit lengthUnit timeUnit
          setup.finalAngularMomentumAboutHinge

/-! ## Derived angular speed and displayed answers -/

/-!
Substituting the printed values into the general inertia and conservation
laws yields

`omega = (0.01 * 400 * 0.50) /
  ((1/3) * 15 * 1.00^2 + 0.01 * 0.50^2) = 800 / 2001`.

This exact angular speed is a derived conclusion, not a premise field.
-/
lemma finalAngularSpeed_exact_readout
    (setup : DoorBulletSetup)
    (hData : MatchesProblemReadouts setup)
    (hBoundary : MatchesCollisionBoundaryConditions setup)
    (hPhysical : HasPhysicalDoorBulletParameters setup)
    (hGeometry : SatisfiesCenterImpactGeometry setup)
    (hInertia : SatisfiesDoorBulletInertiaLaws setup)
    (hMomentum : SatisfiesAngularMomentumConservationAtImpact setup) :
    angularSpeedInRadiansPerSecond setup.finalAngularSpeed =
      800 / 2001 := by
  have hDoorI :
      momentOfInertiaInKilogramMetersSquared
          setup.doorMomentOfInertiaAboutHinge = 5 := by
    change momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters
        setup.doorMomentOfInertiaAboutHinge = 5
    rw [hInertia.uniformDoorAboutHinges]
    change (1 / 3 : ℝ) * massInKilograms setup.doorMass *
        lengthInMeters setup.doorWidth ^ 2 = 5
    rw [hData.doorMassKilograms, hData.doorWidthMeters]
    norm_num
  have hBulletI :
      momentOfInertiaInKilogramMetersSquared
          setup.embeddedBulletMomentOfInertiaAboutHinge = 1 / 400 := by
    change momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters
        setup.embeddedBulletMomentOfInertiaAboutHinge = 1 / 400
    rw [hInertia.embeddedBulletAsPointMass]
    change massInKilograms setup.bulletMass *
        lengthInMeters setup.hingeToImpactDistance ^ 2 = 1 / 400
    rw [hData.bulletMassKilograms, hData.hingeToImpactDistanceMeters]
    norm_num
  have hCombinedI :
      momentOfInertiaInKilogramMetersSquared
          setup.combinedMomentOfInertiaAfterImpact = 2001 / 400 := by
    change momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters
        setup.combinedMomentOfInertiaAfterImpact = 2001 / 400
    rw [hInertia.combinedInertiaIsSum]
    change momentOfInertiaInKilogramMetersSquared
          setup.doorMomentOfInertiaAboutHinge +
        momentOfInertiaInKilogramMetersSquared
          setup.embeddedBulletMomentOfInertiaAboutHinge = 2001 / 400
    rw [hDoorI, hBulletI]
    norm_num
  have hRest :
      angularSpeedInRadiansPerSecond setup.doorInitialAngularSpeed = 0 :=
    hBoundary.doorInitiallyAtRest TimeUnit.seconds
  have hInitialL :
      angularMomentumInKilogramMetersSquaredPerSecond
          setup.initialAngularMomentumAboutHinge = 2 := by
    change angularMomentumReadout MassUnit.kilograms LengthUnit.meters
        TimeUnit.seconds setup.initialAngularMomentumAboutHinge = 2
    rw [hMomentum.initialAngularMomentumLaw]
    change massInKilograms setup.bulletMass *
            speedInMetersPerSecond setup.bulletInitialSpeed *
            lengthInMeters setup.hingeToImpactDistance +
          momentOfInertiaInKilogramMetersSquared
              setup.doorMomentOfInertiaAboutHinge *
            angularSpeedInRadiansPerSecond setup.doorInitialAngularSpeed = 2
    rw [hData.bulletMassKilograms, hData.bulletSpeedMetersPerSecond,
      hData.hingeToImpactDistanceMeters, hDoorI, hRest]
    norm_num
  have hFinalL :
      angularMomentumInKilogramMetersSquaredPerSecond
          setup.finalAngularMomentumAboutHinge =
        (2001 / 400) *
          angularSpeedInRadiansPerSecond setup.finalAngularSpeed := by
    change angularMomentumReadout MassUnit.kilograms LengthUnit.meters
        TimeUnit.seconds setup.finalAngularMomentumAboutHinge = _
    rw [hMomentum.finalAngularMomentumLaw]
    change momentOfInertiaInKilogramMetersSquared
          setup.combinedMomentOfInertiaAfterImpact *
        angularSpeedInRadiansPerSecond setup.finalAngularSpeed = _
    rw [hCombinedI]
  have hConserved :
      angularMomentumInKilogramMetersSquaredPerSecond
          setup.initialAngularMomentumAboutHinge =
        angularMomentumInKilogramMetersSquaredPerSecond
          setup.finalAngularMomentumAboutHinge := by
    exact hMomentum.angularMomentumConserved
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  rw [hInitialL, hFinalL] at hConserved
  norm_num at hConserved ⊢
  linarith

/-- Labels of the four angular-speed choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Numerical value beside each answer label, in radians per second. -/
def displayedAngularSpeedInRadiansPerSecond : AnswerChoice → ℝ
  | .A => 3 / 5
  | .B => 2 / 5
  | .C => 4 / 5
  | .D => 3 / 10

/-- The answer label recorded by the source dataset; this is metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Agreement with a value displayed to the nearest hundredth of a radian per
second.  Half a hundredth is `1/200 rad/s`.
-/
def RoundsToNearestHundredthRadianPerSecond
    (angularSpeed : AngularSpeedQuantity) (displayedValue : ℝ) : Prop :=
  |angularSpeedInRadiansPerSecond angularSpeed - displayedValue| <
    (1 / 200 : ℝ)

/-- The physical final angular speed rounds to the value printed by a choice. -/
def MatchesAnswerChoice
    (setup : DoorBulletSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestHundredthRadianPerSecond setup.finalAngularSpeed
    (displayedAngularSpeedInRadiansPerSecond choice)

/-- A displayed choice is strictly closer than each of the alternatives. -/
def IsUniqueClosestDisplayedChoice
    (setup : DoorBulletSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |angularSpeedInRadiansPerSecond setup.finalAngularSpeed -
        displayedAngularSpeedInRadiansPerSecond choice| <
      |angularSpeedInRadiansPerSecond setup.finalAngularSpeed -
        displayedAngularSpeedInRadiansPerSecond other|

/-!
Formalization of `thm:physics:phyx_mini_0827:target`.  The exact angular
speed, its rounded `0.40 rad/s` value, and choice B occur only in this
conclusion (and the preceding derived lemma), never in the scenario, data,
geometry, inertia, or conservation assumptions.
-/
theorem problem_phyx_mini_0827
    (setup : DoorBulletSetup)
    (hScenario : MatchesDoorBulletScenario setup)
    (hData : MatchesProblemReadouts setup)
    (hFigure : MatchesPrimaryDoorImpactFigure setup)
    (hBoundary : MatchesCollisionBoundaryConditions setup)
    (hPhysical : HasPhysicalDoorBulletParameters setup)
    (hGeometry : SatisfiesCenterImpactGeometry setup)
    (hInertia : SatisfiesDoorBulletInertiaLaws setup)
    (hMomentum : SatisfiesAngularMomentumConservationAtImpact setup) :
    angularSpeedInRadiansPerSecond setup.finalAngularSpeed =
        800 / 2001 ∧
      RoundsToNearestHundredthRadianPerSecond
        setup.finalAngularSpeed (2 / 5) ∧
      MatchesAnswerChoice setup recordedDatasetAnswer ∧
      IsUniqueClosestDisplayedChoice setup recordedDatasetAnswer := by
  have hExact := finalAngularSpeed_exact_readout setup hData hBoundary
    hPhysical hGeometry hInertia hMomentum
  have hRound :
      RoundsToNearestHundredthRadianPerSecond
        setup.finalAngularSpeed (2 / 5) := by
    rw [RoundsToNearestHundredthRadianPerSecond, hExact]
    norm_num [abs_of_nonpos, abs_of_nonneg]
  have hMatch : MatchesAnswerChoice setup recordedDatasetAnswer := by
    simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      displayedAngularSpeedInRadiansPerSecond] using hRound
  have hClosest : IsUniqueClosestDisplayedChoice
      setup recordedDatasetAnswer := by
    intro other hOther
    rw [hExact]
    fin_cases other <;>
      simp_all [recordedDatasetAnswer,
        displayedAngularSpeedInRadiansPerSecond] <;>
      norm_num [abs_of_nonpos, abs_of_nonneg]
  exact ⟨hExact, hRound, hMatch, hClosest⟩

end PhyXMiniProblems.ProblemPhyXMini0827
