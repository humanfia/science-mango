import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Putty dropped onto a vertically suspended spring frame

A `0.150 kg` frame stretches a vertical coil spring by `0.0400 m` at its
frame-only equilibrium.  A `0.200 kg` lump of putty is released from rest
`0.300 m` above the frame's receiving platform.  The putty sticks to the frame
in a short impact, and the combined body subsequently moves on the spring.

The primary image shows a fixed upper support, a vertical coil spring, the
suspended frame and its horizontal bottom platform, a red putty lump above the
platform, and a vertical double-headed arrow labelled `30.0 cm` from the
platform to the putty's initial level.

Masses, lengths, speeds, acceleration magnitudes, and spring stiffness are
unit-independent Physlib quantities.  Real numbers occur below only as
coherent named-unit readouts and dimensionless numerical data.

Assumption/target boundary:

* `MatchesProblemAndFigureReadouts` contains only the given masses, extension,
  drop height, qualitative idealizations, and primary-image observations.
* `MatchesInitialAndTurningPointConditions` states release from rest, the
  frame's pre-impact rest state, and zero speed at a maximum displacement.
* `SatisfiesStaticSpringEquilibrium`, `SatisfiesFreeFallLaw`,
  `SatisfiesImpulsiveStickingCollision`, and
  `SatisfiesPostImpactMechanicalEnergy` are governing mechanics laws.
* `SatisfiesMaximumDisplacementGeometry` relates the spring's extension at the
  turning point to the displacement measured from the old equilibrium.
* There are no previous-part results.  The exact maximum displacement and its
  rounded answer-choice value occur only in conclusions below.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0765

open Dimension

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative speed magnitude.  All modeled motion is along the chosen
downward-positive vertical axis. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative acceleration magnitude, with dimension length/time². -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Spring stiffness, with dimension mass/time² (`N/m` in SI). -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an acceleration magnitude in coherent length/time² units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read spring stiffness in coherent mass/time² units. -/
def stiffnessReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout used for the source masses. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout used for all vertical distances in the mechanics laws. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used for the figure's printed drop-height label. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Metres-per-second readout of a vertical speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metres-per-second-squared readout of the gravitational acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Newton-per-metre readout of the spring stiffness. -/
def stiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  stiffnessReadout MassUnit.kilograms TimeUnit.seconds stiffness

/-! ## Physical roles and primary-image evidence -/

/-- Objects visible in the supplied vertical spring diagram. -/
inductive FigureObject where
  | fixedUpperSupport
  | coilSpring
  | suspendedFrame
  | receivingPlatform
  | puttyLump
  | dropHeightArrow
  deriving DecidableEq, Repr

/-- Text printed in the supplied image. -/
inductive FigureLabel where
  | dropHeight30Point0Centimeters
  deriving DecidableEq, Repr

/-- Distinguished levels at the ends of the displayed height arrow. -/
inductive FigureLevel where
  | puttyInitialLevel
  | receivingPlatformLevel
  deriving DecidableEq, Repr

/-- Orientation vocabulary for the spring axis and receiving platform. -/
inductive Orientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Constitutive idealization of the coil spring. -/
inductive SpringModel where
  | idealMasslessHookean
  | other
  deriving DecidableEq, Repr

/-- Outcome of the putty--frame impact. -/
inductive CollisionOutcome where
  | puttySticksToFrame
  | bodiesSeparate
  deriving DecidableEq, Repr

/-- Comparison between the collision time and the later spring-motion time. -/
inductive CollisionTimeScale where
  | impulsiveRelativeToSpringMotion
  | comparableToSpringMotion
  deriving DecidableEq, Repr

/-- Dissipation model used after the inelastic impact. -/
inductive PostImpactMotionModel where
  | undampedVerticalSpringMotion
  | dissipativeMotion
  deriving DecidableEq, Repr

/-- Qualitative observations transcribed from the supplied bitmap. -/
structure SuppliedVerticalSpringFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  springAxisOrientation : Orientation
  platformOrientation : Orientation
  springConnectsUpperSupportToFrame : Bool
  puttyIsAboveReceivingPlatform : Bool
  dropHeightArrowEndpoints : FigureLevel × FigureLevel

/-!
The physical parameters, collision states, and requested response quantity.

`maximumDownwardDisplacement` is an unconstrained physical length in this
structure.  No field assigns it a numerical value or an answer choice.
-/
structure VerticalSpringPuttySetup where
  frameMass : MassQuantity
  puttyMass : MassQuantity
  springStiffness : SpringStiffnessQuantity
  frameOnlyEquilibriumExtension : LengthQuantity
  dropHeight : LengthQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  puttyReleaseSpeed : SpeedQuantity
  frameSpeedImmediatelyBeforeImpact : SpeedQuantity
  puttySpeedImmediatelyBeforeImpact : SpeedQuantity
  commonSpeedImmediatelyAfterImpact : SpeedQuantity
  combinedSpeedAtMaximumDisplacement : SpeedQuantity
  springExtensionAtMaximumDisplacement : LengthQuantity
  maximumDownwardDisplacement : LengthQuantity
  springModel : SpringModel
  collisionOutcome : CollisionOutcome
  collisionTimeScale : CollisionTimeScale
  postImpactMotionModel : PostImpactMotionModel
  figure : SuppliedVerticalSpringFigure

/-! ## Source data, boundary conditions, and physical parameters -/

/-!
Numerical source data and qualitative facts from the prose and primary image.
The two statements of the drop height are the same given measurement expressed
in the SI metre readout used by the laws and the centimetre readout printed in
the figure.  No requested displacement appears here.
-/
structure MatchesProblemAndFigureReadouts
    (setup : VerticalSpringPuttySetup) : Prop where
  frameMassKilograms : massInKilograms setup.frameMass = 3 / 20
  puttyMassKilograms : massInKilograms setup.puttyMass = 1 / 5
  equilibriumExtensionMeters :
    lengthInMeters setup.frameOnlyEquilibriumExtension = 1 / 25
  dropHeightMeters : lengthInMeters setup.dropHeight = 3 / 10
  dropHeightCentimeters : lengthInCentimeters setup.dropHeight = 30
  springIsIdealAndMassless : setup.springModel = .idealMasslessHookean
  impactIsCompletelyInelastic :
    setup.collisionOutcome = .puttySticksToFrame
  impactIsImpulsive :
    setup.collisionTimeScale = .impulsiveRelativeToSpringMotion
  subsequentMotionIsUndamped :
    setup.postImpactMotionModel = .undampedVerticalSpringMotion
  allDepictedObjectsShown : ∀ object, setup.figure.showsObject object = true
  displayedHeightLabelShown :
    setup.figure.showsLabel .dropHeight30Point0Centimeters = true
  springIsVertical : setup.figure.springAxisOrientation = .vertical
  platformIsHorizontal : setup.figure.platformOrientation = .horizontal
  springJoinsSupportAndFrame :
    setup.figure.springConnectsUpperSupportToFrame = true
  puttyShownAbovePlatform :
    setup.figure.puttyIsAboveReceivingPlatform = true
  heightArrowRunsFromPuttyToPlatform :
    setup.figure.dropHeightArrowEndpoints =
      (.puttyInitialLevel, .receivingPlatformLevel)

/-!
The putty is released from rest, the frame is initially at its static
equilibrium, and the combined body is instantaneously at rest at its maximum
downward displacement.  These are boundary conditions, not a numerical answer.
-/
structure MatchesInitialAndTurningPointConditions
    (setup : VerticalSpringPuttySetup) : Prop where
  puttyReleasedFromRest :
    speedInMetersPerSecond setup.puttyReleaseSpeed = 0
  frameInitiallyAtRest :
    speedInMetersPerSecond setup.frameSpeedImmediatelyBeforeImpact = 0
  combinedBodyAtRestAtMaximum :
    speedInMetersPerSecond setup.combinedSpeedAtMaximumDisplacement = 0

/-!
Strict positivity and nondegeneracy of the independently specified physical
inputs.  Response quantities such as the post-impact speed and maximum
displacement are intentionally absent.
-/
structure HasPhysicalInputParameters
    (setup : VerticalSpringPuttySetup) : Prop where
  frameMassPositive : 0 < massInKilograms setup.frameMass
  puttyMassPositive : 0 < massInKilograms setup.puttyMass
  equilibriumExtensionPositive :
    0 < lengthInMeters setup.frameOnlyEquilibriumExtension
  dropHeightPositive : 0 < lengthInMeters setup.dropHeight
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  springStiffnessPositive :
    0 < stiffnessInNewtonsPerMeter setup.springStiffness

/-! ## Governing mechanics laws -/

/-!
At the frame-only equilibrium, the upward Hooke force balances the frame's
weight.  The equality is required in every coherent mass, length, and time
unit system and does not solve for the stiffness.
-/
structure SatisfiesStaticSpringEquilibrium
    (setup : VerticalSpringPuttySetup) : Prop where
  frameWeightBalancedBySpring :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      stiffnessReadout massUnit timeUnit setup.springStiffness *
          lengthReadout lengthUnit setup.frameOnlyEquilibriumExtension =
        massReadout massUnit setup.frameMass *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAcceleration

/-!
Free fall from the release point to the platform, with negligible air
resistance.  This is the general constant-gravity speed-squared relation and
does not assume the impact speed's solved value.
-/
structure SatisfiesFreeFallLaw
    (setup : VerticalSpringPuttySetup) : Prop where
  freeFallSpeedSquared :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit
            setup.puttySpeedImmediatelyBeforeImpact ^ 2 =
        speedReadout lengthUnit timeUnit setup.puttyReleaseSpeed ^ 2 +
          2 * accelerationReadout lengthUnit timeUnit
                setup.gravitationalAcceleration *
              lengthReadout lengthUnit setup.dropHeight

/-!
One-dimensional downward momentum is conserved during the short sticking
impact.  Spring and gravity impulses are neglected only over this impulsive
stage.  Mechanical energy is deliberately not asserted across the inelastic
collision.
-/
structure SatisfiesImpulsiveStickingCollision
    (setup : VerticalSpringPuttySetup) : Prop where
  downwardMomentumConservation :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.puttyMass *
            speedReadout lengthUnit timeUnit
              setup.puttySpeedImmediatelyBeforeImpact +
          massReadout massUnit setup.frameMass *
            speedReadout lengthUnit timeUnit
              setup.frameSpeedImmediatelyBeforeImpact =
        (massReadout massUnit setup.puttyMass +
            massReadout massUnit setup.frameMass) *
          speedReadout lengthUnit timeUnit
            setup.commonSpeedImmediatelyAfterImpact

/-!
The turning-point spring extension is the frame-only equilibrium extension
plus the downward displacement measured from that old equilibrium position.
-/
structure SatisfiesMaximumDisplacementGeometry
    (setup : VerticalSpringPuttySetup) : Prop where
  extensionAtMaximum : ∀ lengthUnit : LengthUnit,
    lengthReadout lengthUnit
          setup.springExtensionAtMaximumDisplacement =
      lengthReadout lengthUnit setup.frameOnlyEquilibriumExtension +
        lengthReadout lengthUnit setup.maximumDownwardDisplacement

/-!
After sticking, mechanical energy is conserved from the old frame-only
equilibrium (`y = 0`) to the later turning point.  Downward is positive, so
the gravitational-potential change is `-M g y`.  This law contains the generic
kinetic, spring-potential, and gravitational-potential terms, but no solved
displacement or answer-choice value.
-/
structure SatisfiesPostImpactMechanicalEnergy
    (setup : VerticalSpringPuttySetup) : Prop where
  energyConservationToTurningPoint :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      (1 / 2 : ℝ) *
            (massReadout massUnit setup.frameMass +
              massReadout massUnit setup.puttyMass) *
            speedReadout lengthUnit timeUnit
              setup.commonSpeedImmediatelyAfterImpact ^ 2 +
          (1 / 2 : ℝ) *
            stiffnessReadout massUnit timeUnit setup.springStiffness *
            lengthReadout lengthUnit
              setup.frameOnlyEquilibriumExtension ^ 2 =
        (1 / 2 : ℝ) *
              (massReadout massUnit setup.frameMass +
                massReadout massUnit setup.puttyMass) *
              speedReadout lengthUnit timeUnit
                setup.combinedSpeedAtMaximumDisplacement ^ 2 +
            (1 / 2 : ℝ) *
              stiffnessReadout massUnit timeUnit setup.springStiffness *
              lengthReadout lengthUnit
                setup.springExtensionAtMaximumDisplacement ^ 2 -
          (massReadout massUnit setup.frameMass +
              massReadout massUnit setup.puttyMass) *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit setup.maximumDownwardDisplacement

/-! ## Derived mechanics relations -/

/-!
The frame's static extension calibrates the otherwise unspecified spring:
`k = (15/4) g` in coherent SI scalar readouts.
-/
lemma springStiffness_calibrated_by_static_extension
    (setup : VerticalSpringPuttySetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hStatic : SatisfiesStaticSpringEquilibrium setup) :
    stiffnessInNewtonsPerMeter setup.springStiffness =
      (15 / 4 : ℝ) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration := by
  have h := hStatic.frameWeightBalancedBySpring
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    stiffnessInNewtonsPerMeter setup.springStiffness *
        lengthInMeters setup.frameOnlyEquilibriumExtension =
      massInKilograms setup.frameMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration at h
  rw [hReadouts.equilibriumExtensionMeters,
    hReadouts.frameMassKilograms] at h
  norm_num at h ⊢
  linarith

/-! The `0.300 m` fall from rest gives `v_impact² = (3/5) g`. -/
lemma putty_impact_speed_squared
    (setup : VerticalSpringPuttySetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hBoundary : MatchesInitialAndTurningPointConditions setup)
    (hFall : SatisfiesFreeFallLaw setup) :
    speedInMetersPerSecond setup.puttySpeedImmediatelyBeforeImpact ^ 2 =
      (3 / 5 : ℝ) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration := by
  have h := hFall.freeFallSpeedSquared
    LengthUnit.meters TimeUnit.seconds
  change
    speedInMetersPerSecond setup.puttySpeedImmediatelyBeforeImpact ^ 2 =
      speedInMetersPerSecond setup.puttyReleaseSpeed ^ 2 +
        2 * accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.dropHeight at h
  rw [hBoundary.puttyReleasedFromRest, hReadouts.dropHeightMeters] at h
  norm_num at h ⊢
  linarith

/-!
Momentum conservation for the `0.200 kg` putty sticking to the `0.150 kg`
stationary frame gives `v_after = (4/7) v_impact`.
-/
lemma common_speed_immediately_after_impact
    (setup : VerticalSpringPuttySetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hBoundary : MatchesInitialAndTurningPointConditions setup)
    (hCollision : SatisfiesImpulsiveStickingCollision setup) :
    speedInMetersPerSecond setup.commonSpeedImmediatelyAfterImpact =
      (4 / 7 : ℝ) *
        speedInMetersPerSecond setup.puttySpeedImmediatelyBeforeImpact := by
  have h := hCollision.downwardMomentumConservation
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    massInKilograms setup.puttyMass *
          speedInMetersPerSecond setup.puttySpeedImmediatelyBeforeImpact +
        massInKilograms setup.frameMass *
          speedInMetersPerSecond setup.frameSpeedImmediatelyBeforeImpact =
      (massInKilograms setup.puttyMass +
          massInKilograms setup.frameMass) *
        speedInMetersPerSecond setup.commonSpeedImmediatelyAfterImpact at h
  norm_num [hReadouts.puttyMassKilograms,
    hReadouts.frameMassKilograms, hBoundary.frameInitiallyAtRest] at h ⊢
  linarith

/-!
Eliminating stiffness, impact speed, post-impact speed, and gravitational
acceleration from the governing laws gives the quadratic for the displacement
`y` measured in metres.  This relation is derived rather than assumed.
-/
lemma maximumDownwardDisplacement_quadratic
    (setup : VerticalSpringPuttySetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hBoundary : MatchesInitialAndTurningPointConditions setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hStatic : SatisfiesStaticSpringEquilibrium setup)
    (hFall : SatisfiesFreeFallLaw setup)
    (hCollision : SatisfiesImpulsiveStickingCollision setup)
    (hGeometry : SatisfiesMaximumDisplacementGeometry setup)
    (hEnergy : SatisfiesPostImpactMechanicalEnergy setup) :
    2625 * lengthInMeters setup.maximumDownwardDisplacement ^ 2 -
        280 * lengthInMeters setup.maximumDownwardDisplacement - 48 = 0 := by
  have hK :=
    springStiffness_calibrated_by_static_extension setup hReadouts hStatic
  have hImpact :=
    putty_impact_speed_squared setup hReadouts hBoundary hFall
  have hCommon :=
    common_speed_immediately_after_impact
      setup hReadouts hBoundary hCollision
  have hGeom := hGeometry.extensionAtMaximum LengthUnit.meters
  change
    lengthInMeters setup.springExtensionAtMaximumDisplacement =
      lengthInMeters setup.frameOnlyEquilibriumExtension +
        lengthInMeters setup.maximumDownwardDisplacement at hGeom
  have hE := hEnergy.energyConservationToTurningPoint
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    (1 / 2 : ℝ) *
          (massInKilograms setup.frameMass +
            massInKilograms setup.puttyMass) *
          speedInMetersPerSecond setup.commonSpeedImmediatelyAfterImpact ^ 2 +
        (1 / 2 : ℝ) *
          stiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters setup.frameOnlyEquilibriumExtension ^ 2 =
      (1 / 2 : ℝ) *
            (massInKilograms setup.frameMass +
              massInKilograms setup.puttyMass) *
            speedInMetersPerSecond
              setup.combinedSpeedAtMaximumDisplacement ^ 2 +
          (1 / 2 : ℝ) *
            stiffnessInNewtonsPerMeter setup.springStiffness *
            lengthInMeters setup.springExtensionAtMaximumDisplacement ^ 2 -
        (massInKilograms setup.frameMass +
            massInKilograms setup.puttyMass) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.maximumDownwardDisplacement at hE
  norm_num [hReadouts.frameMassKilograms,
    hReadouts.puttyMassKilograms, hBoundary.combinedBodyAtRestAtMaximum,
    hReadouts.equilibriumExtensionMeters, hK, hCommon, hGeom] at hE hImpact ⊢
  nlinarith [hImpact, hPhysical.gravitationalAccelerationPositive]

/-!
The physical length selects the nonnegative root of the quadratic.  The exact
maximum downward distance is about `0.198696 m`.
-/
lemma maximumDownwardDisplacement_exact
    (setup : VerticalSpringPuttySetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hBoundary : MatchesInitialAndTurningPointConditions setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hStatic : SatisfiesStaticSpringEquilibrium setup)
    (hFall : SatisfiesFreeFallLaw setup)
    (hCollision : SatisfiesImpulsiveStickingCollision setup)
    (hGeometry : SatisfiesMaximumDisplacementGeometry setup)
    (hEnergy : SatisfiesPostImpactMechanicalEnergy setup) :
    lengthInMeters setup.maximumDownwardDisplacement =
      (28 + 8 * Real.sqrt 91) / 525 := by
  have hQuadratic :=
    maximumDownwardDisplacement_quadratic
      setup hReadouts hBoundary hPhysical hStatic hFall hCollision hGeometry
        hEnergy
  have hDisplacementNonnegative :
      0 ≤ lengthInMeters setup.maximumDownwardDisplacement := by
    exact_mod_cast
      (setup.maximumDownwardDisplacement UnitChoices.SI).val.property
  have hSqrtSquared : Real.sqrt 91 ^ 2 = 91 := by
    norm_num
  have hSqrtLarge : 7 / 2 < Real.sqrt 91 := by
    nlinarith [Real.sqrt_nonneg (91 : ℝ)]
  have hFactor :
      (525 * lengthInMeters setup.maximumDownwardDisplacement -
          28 - 8 * Real.sqrt 91) *
        (525 * lengthInMeters setup.maximumDownwardDisplacement -
          28 + 8 * Real.sqrt 91) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hFactor with hPositiveRoot | hNegativeRoot
  · field_simp
    linarith
  · exfalso
    nlinarith

/-! ## Displayed choices and formalization target -/

/-- Labels attached to the four distances printed with the exercise. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed maximum downward distances, read in metres. -/
def displayedDistanceInMeters : AnswerChoice → ℝ
  | .A => 371 / 1000
  | .B => 199 / 1000
  | .C => 85 / 1000
  | .D => 264 / 1000

/-- The answer label recorded by the source dataset; this is metadata and is
not used as a premise of the theorem. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement with a displayed distance after rounding to the nearest
millimetre. -/
def RoundsToNearestMillimeter
    (actualMeters displayedMeters : ℝ) : Prop :=
  |actualMeters - displayedMeters| < (1 / 2000 : ℝ)

/-- The physical maximum displacement rounds to the value beside a choice. -/
def MatchesAnswerChoice
    (setup : VerticalSpringPuttySetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestMillimeter
    (lengthInMeters setup.maximumDownwardDisplacement)
    (displayedDistanceInMeters choice)

/-- The selected displayed distance is strictly closer than every alternative. -/
def IsUniqueClosestDisplayedChoice
    (setup : VerticalSpringPuttySetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInMeters setup.maximumDownwardDisplacement -
        displayedDistanceInMeters choice| <
      |lengthInMeters setup.maximumDownwardDisplacement -
        displayedDistanceInMeters other|

/-!
Static spring calibration, free fall, momentum conservation in the sticking
impact, and post-impact mechanical-energy conservation give the exact positive
root `(28 + 8 sqrt 91)/525 m`.  It rounds to `0.199 m`, answer choice B.

This is the formal target corresponding to
`thm:physics:phyx_mini_0765:target`.  Neither the exact root, `0.199 m`, nor
choice B appears in any premise or governing-law field.
-/
theorem problem_phyx_mini_0765
    (setup : VerticalSpringPuttySetup)
    (hReadouts : MatchesProblemAndFigureReadouts setup)
    (hBoundary : MatchesInitialAndTurningPointConditions setup)
    (hPhysical : HasPhysicalInputParameters setup)
    (hStatic : SatisfiesStaticSpringEquilibrium setup)
    (hFall : SatisfiesFreeFallLaw setup)
    (hCollision : SatisfiesImpulsiveStickingCollision setup)
    (hGeometry : SatisfiesMaximumDisplacementGeometry setup)
    (hEnergy : SatisfiesPostImpactMechanicalEnergy setup) :
    lengthInMeters setup.maximumDownwardDisplacement =
        (28 + 8 * Real.sqrt 91) / 525 ∧
      MatchesAnswerChoice setup .B ∧
      IsUniqueClosestDisplayedChoice setup .B := by
  have hExact :=
    maximumDownwardDisplacement_exact
      setup hReadouts hBoundary hPhysical hStatic hFall hCollision hGeometry
        hEnergy
  have hSqrtSquared : Real.sqrt 91 ^ 2 = 91 := by
    norm_num
  have hSqrtNonnegative : 0 ≤ Real.sqrt 91 := Real.sqrt_nonneg 91
  have hSqrtLower : (9539 / 1000 : ℝ) < Real.sqrt 91 := by
    nlinarith
  have hSqrtUpper : Real.sqrt 91 < (9540 / 1000 : ℝ) := by
    nlinarith
  have hLower :
      (397 / 2000 : ℝ) <
        lengthInMeters setup.maximumDownwardDisplacement := by
    rw [hExact]
    nlinarith
  have hUpper :
      lengthInMeters setup.maximumDownwardDisplacement <
        (199 / 1000 : ℝ) := by
    rw [hExact]
    nlinarith
  refine ⟨hExact, ?_, ?_⟩
  · unfold MatchesAnswerChoice RoundsToNearestMillimeter
    simp only [displayedDistanceInMeters]
    rw [abs_of_neg (sub_neg.mpr hUpper)]
    nlinarith
  · unfold IsUniqueClosestDisplayedChoice
    intro other hOther
    rcases other with _ | _ | _ | _
    · simp only [displayedDistanceInMeters]
      rw [abs_of_neg (sub_neg.mpr hUpper)]
      rw [abs_of_neg (by
        linarith :
        lengthInMeters setup.maximumDownwardDisplacement -
            (371 / 1000 : ℝ) < 0)]
      norm_num
    · contradiction
    · simp only [displayedDistanceInMeters]
      rw [abs_of_neg (sub_neg.mpr hUpper)]
      rw [abs_of_pos (by
        linarith :
        0 < lengthInMeters setup.maximumDownwardDisplacement -
            (85 / 1000 : ℝ))]
      linarith
    · simp only [displayedDistanceInMeters]
      rw [abs_of_neg (sub_neg.mpr hUpper)]
      rw [abs_of_neg (by
        linarith :
        lengthInMeters setup.maximumDownwardDisplacement -
            (264 / 1000 : ℝ) < 0)]
      norm_num

end PhyXMiniProblems.ProblemPhyXMini0765
