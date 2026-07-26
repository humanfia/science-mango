import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0713

open Dimension

/-!
# Bullet embedding in a rigid rod-and-block pendulum

A `10 g` bullet travels horizontally into a stationary `2.0 kg` block fixed
to the lower end of a uniform `1.5 kg`, `1.0 m` rod.  The bullet embeds in the
block.  The resulting rigid assembly rotates about a frictionless pivot at the
upper end of the rod and reaches a turning angle of `30°` from the downward
vertical.

The impact and the later swing are deliberately separated.  Angular momentum
about the pivot is conserved during the short inelastic impact, whereas
mechanical energy is conserved only during the subsequent swing.

Masses, lengths, speeds, angular speeds, accelerations, and moments of inertia
are unit-independent Physlib quantities.  Real numbers occur only as explicit
unit readouts, the dimensionless angle in radians, and displayed answer data.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed vertical coordinate with physical dimension length. -/
abbrev HeightCoordinateQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative speed magnitude, with dimension length per time. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative angular-speed magnitude, with dimension inverse time. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative acceleration magnitude, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- An axial moment of inertia, with dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a nonnegative length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed height coordinate in a selected length unit. -/
def heightReadout
    (unit : LengthUnit) (height : HeightCoordinateQuantity) : ℝ :=
  (height {UnitChoices.SI with length := unit}).val

/-- Read a speed in a coherent selected length-per-time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an angular speed in a selected inverse-time unit. -/
def angularSpeedReadout
    (timeUnit : TimeUnit) (angularSpeed : AngularSpeedQuantity) : ℝ :=
  ((angularSpeed {UnitChoices.SI with time := timeUnit}).val : ℝ)

/-- Read an acceleration in a coherent selected length-per-time-squared unit. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a moment of inertia in coherent mass-times-length-squared units. -/
def momentOfInertiaReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit)
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia {UnitChoices.SI with
    mass := massUnit, length := lengthUnit}).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Gram readout used for the prose value of the bullet mass. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre readout of a signed vertical coordinate. -/
def heightInMeters (height : HeightCoordinateQuantity) : ℝ :=
  heightReadout LengthUnit.meters height

/-- Metres-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Radians-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedQuantity) : ℝ :=
  angularSpeedReadout TimeUnit.seconds angularSpeed

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Kilogram-metre-squared readout of an axial moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  momentOfInertiaReadout MassUnit.kilograms LengthUnit.meters inertia

/-! ## Motion stages and primary-figure vocabulary -/

/-- The three configurations separated in the supplied image. -/
inductive MotionStage where
  | beforeImpact
  | justAfterImpact
  | topOfSwing
  deriving DecidableEq, Repr

/-- Physical objects visibly distinguished in image `713.png`. -/
inductive FigureObject where
  | bullet
  | block
  | rod
  | upperPivot
  | ceilingSupport
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the primary image. -/
inductive FigureLabel where
  | bulletMass_mb
  | initialBulletSpeed_v0b
  | blockMass_mB
  | initialBlockSpeed_v0B
  | rodLength_d
  | rodMass_mR
  | postImpactAngularSpeed_omega1
  | postImpactEndSpeed_v1
  | lowerHeight_y1
  | swingAngle_theta
  | upperHeight_y2
  | blockRise_deltaY
  | rodCenterRise_deltaYcm
  | rodVerticalProjection_dCosTheta
  | topAngularSpeed_omega2
  | topEndSpeed_v2
  | requestedInitialBulletSpeed_v0b
  deriving DecidableEq, Repr

/-- Horizontal direction of the incident bullet and immediate post-impact motion. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Orientation of the rod in a panel of the primary image. -/
inductive RodOrientation where
  | downwardVertical
  | displacedClockwise
  deriving DecidableEq, Repr

/-- Idealized condition at the upper support. -/
inductive PivotCondition where
  | frictionless
  | dissipative
  deriving DecidableEq, Repr

/-- Mass-distribution model for the rod. -/
inductive RodModel where
  | uniformRigidSlenderRod
  | masslessConnector
  deriving DecidableEq, Repr

/-- Qualitative result of the bullet--block collision. -/
inductive CollisionOutcome where
  | bulletEmbeddedInBlock
  | bulletRebounds
  | bulletPassesThrough
  deriving DecidableEq, Repr

/-- Raw qualitative and labelling evidence supplied by the primary bitmap. -/
structure RigidPendulumFigure where
  showsObject : MotionStage → FigureObject → Bool
  showsLabel : FigureLabel → Bool
  labelStage : FigureLabel → MotionStage
  incidentDirection : HorizontalDirection
  immediateEndMotionDirection : HorizontalDirection
  rodOrientation : MotionStage → RodOrientation
  pivotAtUpperRodEnd : Bool
  blockAtLowerRodEnd : Bool
  bulletShownEmbeddedAfterImpact : Bool
  angleMeasuredFromDownwardVertical : Bool

/-! ## Physical setup, source data, and figure readouts -/

/-!
All independent quantities used by the two-stage textbook model.  In
particular, `initialBulletSpeed` is an unconstrained dimensionful speed here;
no setup field assigns it an answer-choice value.
-/
structure RigidPendulumImpactSetup where
  figure : RigidPendulumFigure
  pivotCondition : PivotCondition
  rodModel : RodModel
  collisionOutcome : CollisionOutcome
  bulletMass : MassQuantity
  blockMass : MassQuantity
  rodMass : MassQuantity
  rodLength : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  initialBulletSpeed : SpeedQuantity
  initialBlockSpeed : SpeedQuantity
  preImpactPendulumAngularSpeed : AngularSpeedQuantity
  postImpactAngularSpeed : AngularSpeedQuantity
  postImpactEndSpeed : SpeedQuantity
  topAngularSpeed : AngularSpeedQuantity
  topEndSpeed : SpeedQuantity
  lowerBlockHeight_y1 : HeightCoordinateQuantity
  upperBlockHeight_y2 : HeightCoordinateQuantity
  lowerRodCenterHeight : HeightCoordinateQuantity
  upperRodCenterHeight : HeightCoordinateQuantity
  blockRise_deltaY : LengthQuantity
  rodCenterRise_deltaYcm : LengthQuantity
  swingAngleRadians : ℝ
  rodMomentOfInertiaAboutPivot : MomentOfInertiaQuantity
  embeddedAssemblyMomentOfInertiaAboutPivot : MomentOfInertiaQuantity

/-!
Literal numerical readouts from the prose and figure.  The acceleration
`9.8 m/s²` is the usual terrestrial textbook calibration needed to turn the
symbolic model into a numerical speed; it is not printed in the image.
-/
structure MatchesProblemReadouts (setup : RigidPendulumImpactSetup) : Prop where
  bulletMassGrams : massInGrams setup.bulletMass = 10
  bulletMassKilograms : massInKilograms setup.bulletMass = 1 / 100
  blockMassKilograms : massInKilograms setup.blockMass = 2
  rodMassKilograms : massInKilograms setup.rodMass = 3 / 2
  rodLengthMeters : lengthInMeters setup.rodLength = 1
  terrestrialGravity :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 49 / 5
  turningAngleThirtyDegrees : setup.swingAngleRadians = Real.pi / 6

/-!
Rest conditions printed or implied in the three panels.  The first panel
prints `v₀B = 0`; the last prints both `ω₂ = 0` and `v₂ = 0`.
-/
structure MatchesBoundaryConditions (setup : RigidPendulumImpactSetup) : Prop where
  blockInitiallyAtRest : speedInMetersPerSecond setup.initialBlockSpeed = 0
  pendulumInitiallyAtRest :
    angularSpeedInRadiansPerSecond setup.preImpactPendulumAngularSpeed = 0
  topAngularSpeedZero : angularSpeedInRadiansPerSecond setup.topAngularSpeed = 0
  topEndSpeedZero : speedInMetersPerSecond setup.topEndSpeed = 0

/-!
Facts transcribed from the primary image together with the prose
idealizations.  The labels `y₁`, `y₂`, `Δy`, and `Δy_cm` are retained
explicitly.  No numerical value of `v₀b` is included.
-/
structure MatchesScenarioAndPrimaryFigure
    (setup : RigidPendulumImpactSetup) : Prop where
  frictionlessPivot : setup.pivotCondition = .frictionless
  uniformRigidRod : setup.rodModel = .uniformRigidSlenderRod
  bulletSticks : setup.collisionOutcome = .bulletEmbeddedInBlock
  incidentBulletMovesRight : setup.figure.incidentDirection = .right
  lowerEndInitiallyMovesRight :
    setup.figure.immediateEndMotionDirection = .right
  rodInitiallyVertical :
    setup.figure.rodOrientation .beforeImpact = .downwardVertical
  rodStillVerticalJustAfterImpact :
    setup.figure.rodOrientation .justAfterImpact = .downwardVertical
  rodDisplacedClockwiseAtTop :
    setup.figure.rodOrientation .topOfSwing = .displacedClockwise
  pivotAtUpperEnd : setup.figure.pivotAtUpperRodEnd = true
  blockAtLowerEnd : setup.figure.blockAtLowerRodEnd = true
  embeddedBulletVisible : setup.figure.bulletShownEmbeddedAfterImpact = true
  angleFromVertical : setup.figure.angleMeasuredFromDownwardVertical = true
  allLabelsShown : ∀ label, setup.figure.showsLabel label = true
  bulletShownBeforeImpact :
    setup.figure.showsObject .beforeImpact .bullet = true
  blockShownInEveryStage :
    ∀ stage, setup.figure.showsObject stage .block = true
  rodShownInEveryStage :
    ∀ stage, setup.figure.showsObject stage .rod = true
  pivotShownInEveryStage :
    ∀ stage, setup.figure.showsObject stage .upperPivot = true
  bulletMassLabelStage :
    setup.figure.labelStage .bulletMass_mb = .beforeImpact
  requestedSpeedLabelStage :
    setup.figure.labelStage .requestedInitialBulletSpeed_v0b = .topOfSwing
  omegaOneLabelStage :
    setup.figure.labelStage .postImpactAngularSpeed_omega1 = .justAfterImpact
  omegaTwoLabelStage :
    setup.figure.labelStage .topAngularSpeed_omega2 = .topOfSwing

/-- Positivity and nondegeneracy assumptions for the physical experiment. -/
structure HasPhysicalParameters (setup : RigidPendulumImpactSetup) : Prop where
  bulletMassPositive : 0 < massInKilograms setup.bulletMass
  blockMassPositive : 0 < massInKilograms setup.blockMass
  rodMassPositive : 0 < massInKilograms setup.rodMass
  rodLengthPositive : 0 < lengthInMeters setup.rodLength
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  initialBulletSpeedPositive :
    0 < speedInMetersPerSecond setup.initialBulletSpeed
  postImpactAngularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond setup.postImpactAngularSpeed
  embeddedAssemblyInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.embeddedAssemblyMomentOfInertiaAboutPivot

/-! ## Governing geometry and mechanics -/

/-!
Rigid rotation relates the lower-end tangential speed to angular speed at
each relevant stage.  These are kinematic laws, not numerical speed answers.
-/
structure SatisfiesRigidRotationKinematics
    (setup : RigidPendulumImpactSetup) : Prop where
  initialEndSpeed :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.initialBlockSpeed =
        lengthReadout lengthUnit setup.rodLength *
          angularSpeedReadout timeUnit setup.preImpactPendulumAngularSpeed
  postImpactEndSpeed :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.postImpactEndSpeed =
        lengthReadout lengthUnit setup.rodLength *
          angularSpeedReadout timeUnit setup.postImpactAngularSpeed
  topEndSpeed :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit setup.topEndSpeed =
        lengthReadout lengthUnit setup.rodLength *
          angularSpeedReadout timeUnit setup.topAngularSpeed

/-!
Geometry of a rod rotating through `θ` from the downward vertical.  The lower
end rises by `d(1-cos θ)`, while the center of mass of a uniform rod rises by
`(d/2)(1-cos θ)`.  The `y₁` and `y₂` relation records the figure's two height
labels rather than defining away either rise.
-/
structure SatisfiesSwingGeometry
    (setup : RigidPendulumImpactSetup) : Prop where
  blockRiseFromHeights :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit setup.blockRise_deltaY =
        heightReadout lengthUnit setup.upperBlockHeight_y2 -
          heightReadout lengthUnit setup.lowerBlockHeight_y1
  rodCenterRiseFromHeights :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit setup.rodCenterRise_deltaYcm =
        heightReadout lengthUnit setup.upperRodCenterHeight -
          heightReadout lengthUnit setup.lowerRodCenterHeight
  blockRiseFromAngle :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit setup.blockRise_deltaY =
        lengthReadout lengthUnit setup.rodLength *
          (1 - Real.cos setup.swingAngleRadians)
  rodCenterRiseFromAngle :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit setup.rodCenterRise_deltaYcm =
        (lengthReadout lengthUnit setup.rodLength / 2) *
          (1 - Real.cos setup.swingAngleRadians)

/-!
The uniform rod has pivot inertia `(1/3)m_R d²`; after the bullet sticks, the
block and bullet are point masses at distance `d`.  Both formulas are required
in every coherent mass/length unit choice.
-/
structure SatisfiesRigidAssemblyInertiaModel
    (setup : RigidPendulumImpactSetup) : Prop where
  uniformRodInertia :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.rodMomentOfInertiaAboutPivot =
        (1 / 3 : ℝ) * massReadout massUnit setup.rodMass *
          lengthReadout lengthUnit setup.rodLength ^ 2
  embeddedAssemblyInertia :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit),
      momentOfInertiaReadout massUnit lengthUnit
          setup.embeddedAssemblyMomentOfInertiaAboutPivot =
        momentOfInertiaReadout massUnit lengthUnit
            setup.rodMomentOfInertiaAboutPivot +
          (massReadout massUnit setup.blockMass +
              massReadout massUnit setup.bulletMass) *
            lengthReadout lengthUnit setup.rodLength ^ 2

/-!
Angular momentum about the pivot during the short collision.  The support
force has zero moment about the pivot.  The rod and block terms are retained
before impact even though the boundary data later set them to rest.
-/
structure SatisfiesAngularMomentumConservationAtImpact
    (setup : RigidPendulumImpactSetup) : Prop where
  angularMomentumBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.bulletMass *
            speedReadout lengthUnit timeUnit setup.initialBulletSpeed *
            lengthReadout lengthUnit setup.rodLength +
          massReadout massUnit setup.blockMass *
            speedReadout lengthUnit timeUnit setup.initialBlockSpeed *
            lengthReadout lengthUnit setup.rodLength +
          momentOfInertiaReadout massUnit lengthUnit
              setup.rodMomentOfInertiaAboutPivot *
            angularSpeedReadout timeUnit setup.preImpactPendulumAngularSpeed =
        momentOfInertiaReadout massUnit lengthUnit
            setup.embeddedAssemblyMomentOfInertiaAboutPivot *
          angularSpeedReadout timeUnit setup.postImpactAngularSpeed

/-!
Mechanical energy is conserved from just after embedding to the turning
point.  It is intentionally not asserted across the inelastic impact.  The
right side retains the top rotational kinetic term even though `ω₂ = 0` is a
separate boundary readout.
-/
structure SatisfiesMechanicalEnergyConservationDuringSwing
    (setup : RigidPendulumImpactSetup) : Prop where
  energyBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      (1 / 2 : ℝ) *
            momentOfInertiaReadout massUnit lengthUnit
              setup.embeddedAssemblyMomentOfInertiaAboutPivot *
            angularSpeedReadout timeUnit setup.postImpactAngularSpeed ^ 2 =
        (1 / 2 : ℝ) *
              momentOfInertiaReadout massUnit lengthUnit
                setup.embeddedAssemblyMomentOfInertiaAboutPivot *
              angularSpeedReadout timeUnit setup.topAngularSpeed ^ 2 +
          (massReadout massUnit setup.blockMass +
              massReadout massUnit setup.bulletMass) *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit setup.blockRise_deltaY +
          massReadout massUnit setup.rodMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit setup.rodCenterRise_deltaYcm

/-!
Eliminating the intermediate angular speed gives a squared relation for the
unknown incident speed.  This is a derived conclusion, not a law field.
-/
lemma initialBulletSpeed_squared_balance
    (setup : RigidPendulumImpactSetup)
    (hBoundary : MatchesBoundaryConditions setup)
    (hMomentum : SatisfiesAngularMomentumConservationAtImpact setup)
    (hEnergy : SatisfiesMechanicalEnergyConservationDuringSwing setup) :
    (massInKilograms setup.bulletMass *
        speedInMetersPerSecond setup.initialBulletSpeed *
        lengthInMeters setup.rodLength) ^ 2 =
      2 * momentOfInertiaInKilogramMetersSquared
          setup.embeddedAssemblyMomentOfInertiaAboutPivot *
        ((massInKilograms setup.blockMass +
              massInKilograms setup.bulletMass) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.blockRise_deltaY +
          massInKilograms setup.rodMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.rodCenterRise_deltaYcm) := by
  rcases hBoundary with ⟨hBlock, hPendulum, hTopOmega, _⟩
  have hM := hMomentum.angularMomentumBalance
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hE := hEnergy.energyBalance
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change speedReadout LengthUnit.meters TimeUnit.seconds
      setup.initialBlockSpeed = 0 at hBlock
  change angularSpeedReadout TimeUnit.seconds
      setup.preImpactPendulumAngularSpeed = 0 at hPendulum
  change angularSpeedReadout TimeUnit.seconds setup.topAngularSpeed = 0 at hTopOmega
  rw [hBlock, hPendulum] at hM
  rw [hTopOmega] at hE
  simp only [mul_zero, zero_mul, add_zero, zero_add,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hM hE
  simp only [massInKilograms, speedInMetersPerSecond, lengthInMeters,
    accelerationInMetersPerSecondSquared,
    momentOfInertiaInKilogramMetersSquared] at ⊢
  rw [hM, ← hE]
  ring

/-!
Substitution of the standard rigid-body model and the printed data yields the
exact SI expression below.  `Real.cos_pi_div_six` can later reduce its angle
factor to `√3 / 2`.
-/
lemma initialBulletSpeed_exact_standard_model_readout
    (setup : RigidPendulumImpactSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hBoundary : MatchesBoundaryConditions setup)
    (hPhysical : HasPhysicalParameters setup)
    (hGeometry : SatisfiesSwingGeometry setup)
    (hInertia : SatisfiesRigidAssemblyInertiaModel setup)
    (hMomentum : SatisfiesAngularMomentumConservationAtImpact setup)
    (hEnergy : SatisfiesMechanicalEnergyConservationDuringSwing setup) :
    speedInMetersPerSecond setup.initialBulletSpeed =
      251 * Real.sqrt
        ((2 * (69 / 25 : ℝ) * (49 / 5 : ℝ) *
            (1 - Real.cos (Real.pi / 6))) /
          (251 / 100 : ℝ)) := by
  have hSq :=
    initialBulletSpeed_squared_balance setup hBoundary hMomentum hEnergy
  have hBlockRise := hGeometry.blockRiseFromAngle LengthUnit.meters
  have hRodRise := hGeometry.rodCenterRiseFromAngle LengthUnit.meters
  have hRodI :=
    hInertia.uniformRodInertia MassUnit.kilograms LengthUnit.meters
  have hAssemblyI :=
    hInertia.embeddedAssemblyInertia MassUnit.kilograms LengthUnit.meters
  change lengthInMeters setup.blockRise_deltaY =
      lengthInMeters setup.rodLength *
        (1 - Real.cos setup.swingAngleRadians) at hBlockRise
  change lengthInMeters setup.rodCenterRise_deltaYcm =
      (lengthInMeters setup.rodLength / 2) *
        (1 - Real.cos setup.swingAngleRadians) at hRodRise
  change momentOfInertiaInKilogramMetersSquared
      setup.rodMomentOfInertiaAboutPivot =
        (1 / 3 : ℝ) * massInKilograms setup.rodMass *
          lengthInMeters setup.rodLength ^ 2 at hRodI
  change momentOfInertiaInKilogramMetersSquared
      setup.embeddedAssemblyMomentOfInertiaAboutPivot =
        momentOfInertiaInKilogramMetersSquared
            setup.rodMomentOfInertiaAboutPivot +
          (massInKilograms setup.blockMass +
              massInKilograms setup.bulletMass) *
            lengthInMeters setup.rodLength ^ 2 at hAssemblyI
  rw [hReadouts.rodLengthMeters, hReadouts.turningAngleThirtyDegrees] at hBlockRise
  rw [hReadouts.rodLengthMeters, hReadouts.turningAngleThirtyDegrees] at hRodRise
  rw [hReadouts.rodMassKilograms, hReadouts.rodLengthMeters] at hRodI
  norm_num at hRodI
  rw [hRodI, hReadouts.blockMassKilograms, hReadouts.bulletMassKilograms,
    hReadouts.rodLengthMeters] at hAssemblyI
  norm_num at hAssemblyI
  rw [hReadouts.bulletMassKilograms, hReadouts.rodLengthMeters,
    hAssemblyI, hReadouts.blockMassKilograms,
    hReadouts.terrestrialGravity, hBlockRise,
    hReadouts.rodMassKilograms, hRodRise] at hSq
  let radicand : ℝ :=
    (2 * (69 / 25 : ℝ) * (49 / 5 : ℝ) *
        (1 - Real.cos (Real.pi / 6))) / (251 / 100 : ℝ)
  have hCos : 0 ≤ 1 - Real.cos (Real.pi / 6) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hRadicand : 0 ≤ radicand := by
    dsimp [radicand]
    positivity
  have hSqrtSq : (Real.sqrt radicand) ^ 2 = radicand :=
    Real.sq_sqrt hRadicand
  have hSquareIdentity :
      speedInMetersPerSecond setup.initialBulletSpeed ^ 2 =
        (251 * Real.sqrt radicand) ^ 2 := by
    rw [mul_pow, hSqrtSq]
    dsimp [radicand]
    field_simp at hSq ⊢
    nlinarith [hSq]
  have hSpeed : 0 < speedInMetersPerSecond setup.initialBulletSpeed :=
    hPhysical.initialBulletSpeedPositive
  have hRhs : 0 ≤ 251 * Real.sqrt radicand := by positivity
  change speedInMetersPerSecond setup.initialBulletSpeed =
    251 * Real.sqrt radicand
  nlinarith [hSquareIdentity]

/-! ## Displayed answers, dataset metadata, and physical target -/

/-- Labels of the four displayed speed choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Numerical value printed beside each answer label, in metres per second. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 240
  | .B => 245
  | .C => 251
  | .D => 262

/-- The answer label recorded in the source dataset; this is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a displayed integral speed after rounding to the nearest `m/s`. -/
def RoundsToNearestMeterPerSecond
    (speed : SpeedQuantity) (displayedSpeed : ℝ) : Prop :=
  |speedInMetersPerSecond speed - displayedSpeed| < (1 / 2 : ℝ)

/-- The physical incident speed rounds to the number printed by a choice. -/
def MatchesAnswerChoice
    (setup : RigidPendulumImpactSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestMeterPerSecond setup.initialBulletSpeed
    (displayedSpeedInMetersPerSecond choice)

/-- A displayed choice is strictly closer than each of the other choices. -/
def IsUniqueClosestDisplayedChoice
    (setup : RigidPendulumImpactSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |speedInMetersPerSecond setup.initialBulletSpeed -
        displayedSpeedInMetersPerSecond choice| <
      |speedInMetersPerSecond setup.initialBulletSpeed -
        displayedSpeedInMetersPerSecond other|

/-!
Formalization of `thm:physics:phyx_mini_0713:target`.  The standard inertia,
impact, geometry, and energy equations give the exact incident speed below,
approximately `426.51 m/s`.  Consequently none of the four displayed speeds
is the physical result, even to the stated nearest-`m/s` tolerance.

The source dataset's recorded choice C remains available only through
`recordedDatasetAnswer`; neither that label nor its printed value occurs in a
premise.  In particular, the physically unsupported `251 m/s` is not asserted
as a target conclusion.
-/
theorem problem_phyx_mini_0713
    (setup : RigidPendulumImpactSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hBoundary : MatchesBoundaryConditions setup)
    (hScenario : MatchesScenarioAndPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hKinematics : SatisfiesRigidRotationKinematics setup)
    (hGeometry : SatisfiesSwingGeometry setup)
    (hInertia : SatisfiesRigidAssemblyInertiaModel setup)
    (hMomentum : SatisfiesAngularMomentumConservationAtImpact setup)
    (hEnergy : SatisfiesMechanicalEnergyConservationDuringSwing setup) :
    speedInMetersPerSecond setup.initialBulletSpeed =
        251 * Real.sqrt
          ((2 * (69 / 25 : ℝ) * (49 / 5 : ℝ) *
              (1 - Real.cos (Real.pi / 6))) /
            (251 / 100 : ℝ)) ∧
      (∀ choice : AnswerChoice, ¬ MatchesAnswerChoice setup choice) := by
  constructor
  · exact initialBulletSpeed_exact_standard_model_readout setup hReadouts
      hBoundary hPhysical hGeometry hInertia hMomentum hEnergy
  · have hExact :=
      initialBulletSpeed_exact_standard_model_readout setup hReadouts
        hBoundary hPhysical hGeometry hInertia hMomentum hEnergy
    let radicand : ℝ :=
      (2 * (69 / 25 : ℝ) * (49 / 5 : ℝ) *
          (1 - Real.cos (Real.pi / 6))) / (251 / 100 : ℝ)
    have hSqrtThree : Real.sqrt 3 < (9 / 5 : ℝ) := by
      have hSq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
        Real.sq_sqrt (by norm_num)
      have hNonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have hAngle : (1 / 10 : ℝ) < 1 - Real.cos (Real.pi / 6) := by
      rw [Real.cos_pi_div_six]
      nlinarith [hSqrtThree]
    have hRadicandLower : (6 / 5 : ℝ) ^ 2 < radicand := by
      dsimp [radicand]
      norm_num
      nlinarith [hAngle]
    have hRadicand : 0 ≤ radicand := by
      nlinarith [hRadicandLower]
    have hSqrtSq : (Real.sqrt radicand) ^ 2 = radicand :=
      Real.sq_sqrt hRadicand
    have hSqrtNonneg : 0 ≤ Real.sqrt radicand := Real.sqrt_nonneg _
    have hSqrtLower : (6 / 5 : ℝ) < Real.sqrt radicand := by
      nlinarith [hRadicandLower, hSqrtSq]
    change speedInMetersPerSecond setup.initialBulletSpeed =
      251 * Real.sqrt radicand at hExact
    have hSpeedLower :
        300 < speedInMetersPerSecond setup.initialBulletSpeed := by
      rw [hExact]
      nlinarith [hSqrtLower]
    intro choice hMatch
    change |speedInMetersPerSecond setup.initialBulletSpeed -
        displayedSpeedInMetersPerSecond choice| < (1 / 2 : ℝ) at hMatch
    have hDisplayed : displayedSpeedInMetersPerSecond choice ≤ 262 := by
      cases choice <;> norm_num [displayedSpeedInMetersPerSecond]
    have hDiff : 0 ≤ speedInMetersPerSecond setup.initialBulletSpeed -
        displayedSpeedInMetersPerSecond choice := by
      linarith
    rw [abs_of_nonneg hDiff] at hMatch
    linarith

end PhyXMiniProblems.ProblemPhyXMini0713
