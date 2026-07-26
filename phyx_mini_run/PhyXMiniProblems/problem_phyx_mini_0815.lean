import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0815

open Dimension

/-!
# Ballistic pendulum

A bullet of mass `m_B`, moving horizontally with speed `v_1`, embeds in a
suspended wooden block of mass `m_W`.  The compound bullet--block body leaves
the perfectly inelastic collision with horizontal speed `v_2`, then swings
upward through a vertical height `h` and comes instantaneously to rest.

The collision and the later swing are deliberately modeled as two different
physical phases.  Horizontal momentum is conserved during the short impact;
mechanical energy is conserved only during the subsequent swing.  In
particular, kinetic energy is not assumed to be conserved across the
perfectly inelastic collision.

Mass, length, speed, acceleration, momentum, and energy are represented by
unit-independent Physlib quantities.  Real numbers occur only as coherent
unit readouts and in the printed answer formulas.

Assumption/target split:

* `MatchesStatedScenario` records the perfectly inelastic outcome, directions,
  suspension, initial rest condition, and turning-point boundary condition;
* `MatchesPrimaryFigure` records the two coordinate axes, three labeled
  stages, objects, arrows, symbolic labels, and height marker in image 815;
* `HasPhysicalParameters` records positivity and nondegeneracy;
* `SatisfiesStickingCollisionMomentumLaws` states mass additivity, momentum
  factorization, and horizontal momentum conservation during impact;
* `SatisfiesConservativePendulumSwingLaws` states the kinetic-energy,
  gravitational-potential-energy, and post-impact energy laws; and
* the requested formula for `v_1` occurs only in derived conclusions.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- Gravitational acceleration has dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent vertical height. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A signed one-dimensional momentum component along the displayed x-axis. -/
abbrev HorizontalMomentumQuantity : Type := Dimensionful (Momentum 1)

/-- Mechanical energy with Physlib's energy dimension. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read the unique component of a one-dimensional momentum quantity. -/
def horizontalMomentumReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (momentum : HorizontalMomentumQuantity) : ℝ :=
  (momentum {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val 0

/-- Read energy in the coherent unit induced by selected mechanical units. -/
def energyReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (energy : EnergyQuantity) : ℝ :=
  (energy {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout of a physical height. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre-per-second readout of a speed magnitude. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Physical stages and primary-figure vocabulary -/

/-- Separate bodies present immediately before the impact. -/
inductive CollisionBody where
  | bullet
  | woodBlock
  deriving DecidableEq, Fintype, Repr

/-- Stages labeled in the supplied ballistic-pendulum image. -/
inductive FigureStage where
  | beforeCollision
  | immediatelyAfterCollision
  | topOfSwing
  deriving DecidableEq, Fintype, Repr

/-- The two states used in the post-impact energy balance. -/
inductive SwingStage where
  | immediatelyAfterCollision
  | topOfSwing
  deriving DecidableEq, Fintype, Repr

/-- Coordinate axes explicitly drawn in both panels. -/
inductive DiagramAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Positive senses of the displayed coordinate axes. -/
inductive AxisPositiveDirection where
  | rightward
  | upward
  deriving DecidableEq, Repr

/-- Horizontal directions used by the two velocity arrows. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Vertical direction of the measured pendulum rise. -/
inductive VerticalDirection where
  | downward
  | upward
  deriving DecidableEq, Repr

/-- Qualitative collision outcome. -/
inductive CollisionOutcome where
  | bulletEmbedsInBlock
  | bulletAndBlockSeparate
  deriving DecidableEq, Repr

/-- Support geometry stated in the problem and shown in the image. -/
inductive PendulumSupport where
  | blockSuspendedByTwoWires
  | unsupportedBlock
  deriving DecidableEq, Repr

/-- Impact-scale external-impulse idealization used for x-momentum balance. -/
inductive CollisionImpulseModel where
  | negligibleExternalHorizontalImpulse
  | includesExternalHorizontalImpulse
  deriving DecidableEq, Repr

/-- Objects and construction lines visible in image `815.png`. -/
inductive FigureObject where
  | bullet
  | woodBlock
  | suspensionWires
  | embeddedComposite
  | initialVelocityArrow
  | postImpactVelocityArrow
  | swingArc
  | heightMarker
  deriving DecidableEq, Fintype, Repr

/-- Symbolic and textual labels printed in image `815.png`. -/
inductive FigureLabel where
  | bulletMass_mB
  | woodMass_mW
  | initialSpeed_v1
  | postImpactSpeed_v2
  | combinedMass_mB_add_mW
  | riseHeight_h
  | beforeCollisionText
  | immediatelyAfterCollisionText
  | topOfSwingText
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative transcription of the primary raster.  No field contains
the requested initial-speed formula or a numerical value for an unknown.
-/
structure BallisticPendulumFigure where
  axisShownAt : FigureStage → DiagramAxis → Bool
  positiveAxisDirection : DiagramAxis → AxisPositiveDirection
  objectShownAt : FigureStage → FigureObject → Bool
  labelShown : FigureLabel → Bool
  labelStage : FigureLabel → FigureStage
  bulletIsLeftOfBlockBeforeCollision : Bool
  initialArrowDirection : HorizontalDirection
  postImpactArrowDirection : HorizontalDirection
  bulletShownEmbeddedImmediatelyAfterCollision : Bool
  topOfSwingAboveImpactLevel : Bool
  heightMarkerParallelToYAxis : Bool

/-!
Independent physical quantities for the two-stage experiment.  In particular,
the bullet's initial speed is an unconstrained physical speed; it is not
defined from `m_B`, `m_W`, `g`, `h`, or an answer choice.
-/
structure BallisticPendulumSetup where
  figure : BallisticPendulumFigure
  bodyMass : CollisionBody → MassQuantity
  compositeMass : MassQuantity
  speedBeforeCollision : CollisionBody → SpeedQuantity
  swingSpeed : SwingStage → SpeedQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  maximumVerticalRise : LengthQuantity
  horizontalMomentumBeforeCollision : HorizontalMomentumQuantity
  horizontalMomentumAfterCollision : HorizontalMomentumQuantity
  translationalKineticEnergy : SwingStage → EnergyQuantity
  gravitationalPotentialEnergy : SwingStage → EnergyQuantity
  collisionOutcome : CollisionOutcome
  support : PendulumSupport
  collisionImpulseModel : CollisionImpulseModel
  bulletInitialDirection : HorizontalDirection
  compositeInitialDirection : HorizontalDirection
  riseDirection : VerticalDirection

/-! ## Scenario facts, figure evidence, and governing laws -/

/-- Qualitative scenario assumptions and the two zero-speed boundary states. -/
structure MatchesStatedScenario (setup : BallisticPendulumSetup) : Prop where
  blockIsSuspended : setup.support = .blockSuspendedByTwoWires
  impactIsPerfectlyInelastic :
    setup.collisionOutcome = .bulletEmbedsInBlock
  shortImpactHasNegligibleExternalHorizontalImpulse :
    setup.collisionImpulseModel = .negligibleExternalHorizontalImpulse
  bulletInitiallyMovesRight : setup.bulletInitialDirection = .rightward
  compositeInitiallyMovesRight :
    setup.compositeInitialDirection = .rightward
  pendulumRisesUpward : setup.riseDirection = .upward
  woodenBlockInitiallyAtRest :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit
        (setup.speedBeforeCollision .woodBlock) = 0
  compositeStopsAtTopOfSwing :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit
        (setup.swingSpeed .topOfSwing) = 0

/-! Facts read directly from the axes, labels, arrows, and geometry in image 815. -/
structure MatchesPrimaryFigure (setup : BallisticPendulumSetup) : Prop where
  bothAxesShownAtEveryStage :
    ∀ (stage : FigureStage) (axis : DiagramAxis),
      setup.figure.axisShownAt stage axis = true
  positiveXPointsRight :
    setup.figure.positiveAxisDirection .x = .rightward
  positiveYPointsUp :
    setup.figure.positiveAxisDirection .y = .upward
  everyPrintedLabelIsShown :
    ∀ label : FigureLabel, setup.figure.labelShown label = true
  bulletMassLabelBefore :
    setup.figure.labelStage .bulletMass_mB = .beforeCollision
  woodMassLabelBefore :
    setup.figure.labelStage .woodMass_mW = .beforeCollision
  initialSpeedLabelBefore :
    setup.figure.labelStage .initialSpeed_v1 = .beforeCollision
  beforeCollisionCaptionBefore :
    setup.figure.labelStage .beforeCollisionText = .beforeCollision
  postImpactSpeedLabelImmediatelyAfter :
    setup.figure.labelStage .postImpactSpeed_v2 = .immediatelyAfterCollision
  combinedMassLabelImmediatelyAfter :
    setup.figure.labelStage .combinedMass_mB_add_mW =
      .immediatelyAfterCollision
  immediatelyAfterCaptionImmediatelyAfter :
    setup.figure.labelStage .immediatelyAfterCollisionText =
      .immediatelyAfterCollision
  heightLabelAtTop :
    setup.figure.labelStage .riseHeight_h = .topOfSwing
  topCaptionAtTop :
    setup.figure.labelStage .topOfSwingText = .topOfSwing
  bulletShownBefore :
    setup.figure.objectShownAt .beforeCollision .bullet = true
  woodBlockShownBefore :
    setup.figure.objectShownAt .beforeCollision .woodBlock = true
  suspensionShownBefore :
    setup.figure.objectShownAt .beforeCollision .suspensionWires = true
  compositeShownImmediatelyAfter :
    setup.figure.objectShownAt .immediatelyAfterCollision
      .embeddedComposite = true
  swingArcShown :
    setup.figure.objectShownAt .topOfSwing .swingArc = true
  heightMarkerShown :
    setup.figure.objectShownAt .topOfSwing .heightMarker = true
  bulletStartsLeftOfBlock :
    setup.figure.bulletIsLeftOfBlockBeforeCollision = true
  initialArrowPointsRight : setup.figure.initialArrowDirection = .rightward
  postImpactArrowPointsRight :
    setup.figure.postImpactArrowDirection = .rightward
  bulletIsDrawnEmbedded :
    setup.figure.bulletShownEmbeddedImmediatelyAfterCollision = true
  topPositionIsHigher : setup.figure.topOfSwingAboveImpactLevel = true
  heightMarkerFollowsYAxis : setup.figure.heightMarkerParallelToYAxis = true

/-- Positivity and nondegeneracy conditions selecting the physical branches. -/
structure HasPhysicalParameters (setup : BallisticPendulumSetup) : Prop where
  eachBodyMassPositive :
    ∀ body : CollisionBody, 0 < massInKilograms (setup.bodyMass body)
  compositeMassPositive : 0 < massInKilograms setup.compositeMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  maximumRiseNonnegative :
    0 ≤ lengthInMeters setup.maximumVerticalRise
  bulletInitialSpeedPositive :
    0 < speedInMetersPerSecond (setup.speedBeforeCollision .bullet)
  postImpactSpeedNonnegative :
    0 ≤ speedInMetersPerSecond
      (setup.swingSpeed .immediatelyAfterCollision)

/-!
Mass additivity and one-dimensional x-momentum conservation during the short
sticking collision.  Momentum is stated in every coherent choice of mass,
length, and time units.  No field assigns the unknown bullet speed.
-/
structure SatisfiesStickingCollisionMomentumLaws
    (setup : BallisticPendulumSetup) : Prop where
  compositeMassIsSum :
    ∀ massUnit : MassUnit,
      massReadout massUnit setup.compositeMass =
        massReadout massUnit (setup.bodyMass .bullet) +
          massReadout massUnit (setup.bodyMass .woodBlock)
  momentumBeforeFactorization :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      horizontalMomentumReadout massUnit lengthUnit timeUnit
          setup.horizontalMomentumBeforeCollision =
        massReadout massUnit (setup.bodyMass .bullet) *
            speedReadout lengthUnit timeUnit
              (setup.speedBeforeCollision .bullet) +
          massReadout massUnit (setup.bodyMass .woodBlock) *
            speedReadout lengthUnit timeUnit
              (setup.speedBeforeCollision .woodBlock)
  momentumAfterFactorization :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      horizontalMomentumReadout massUnit lengthUnit timeUnit
          setup.horizontalMomentumAfterCollision =
        massReadout massUnit setup.compositeMass *
          speedReadout lengthUnit timeUnit
            (setup.swingSpeed .immediatelyAfterCollision)
  horizontalMomentumConservation :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      horizontalMomentumReadout massUnit lengthUnit timeUnit
          setup.horizontalMomentumBeforeCollision =
        horizontalMomentumReadout massUnit lengthUnit timeUnit
          setup.horizontalMomentumAfterCollision

/-!
Kinetic energy, gravitational potential-energy gain, and mechanical-energy
conservation for the compound body from immediately after impact to the top
of the swing.  Energy conservation is not asserted across the inelastic
collision.
-/
structure SatisfiesConservativePendulumSwingLaws
    (setup : BallisticPendulumSetup) : Prop where
  translationalKineticEnergyLaw :
    ∀ (stage : SwingStage) (massUnit : MassUnit)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      2 * energyReadout massUnit lengthUnit timeUnit
          (setup.translationalKineticEnergy stage) =
        massReadout massUnit setup.compositeMass *
          speedReadout lengthUnit timeUnit (setup.swingSpeed stage) ^ 2
  gravitationalPotentialEnergyGain :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
            (setup.gravitationalPotentialEnergy .topOfSwing) -
          energyReadout massUnit lengthUnit timeUnit
            (setup.gravitationalPotentialEnergy .immediatelyAfterCollision) =
        massReadout massUnit setup.compositeMass *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAccelerationMagnitude *
          lengthReadout lengthUnit setup.maximumVerticalRise
  mechanicalEnergyConservation :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
            (setup.translationalKineticEnergy .immediatelyAfterCollision) +
          energyReadout massUnit lengthUnit timeUnit
            (setup.gravitationalPotentialEnergy .immediatelyAfterCollision) =
        energyReadout massUnit lengthUnit timeUnit
            (setup.translationalKineticEnergy .topOfSwing) +
          energyReadout massUnit lengthUnit timeUnit
            (setup.gravitationalPotentialEnergy .topOfSwing)

/-! ## Derived relations and answer metadata -/

/-!
Energy conservation during the swing selects the nonnegative square-root
branch `v_2 = sqrt (2 g h)`.  This is an intermediate conclusion, not an
assumption of the collision model.
-/
lemma postImpactSpeed_eq_sqrt_two_g_h
    (setup : BallisticPendulumSetup)
    (hScenario : MatchesStatedScenario setup)
    (hPhysical : HasPhysicalParameters setup)
    (hEnergy : SatisfiesConservativePendulumSwingLaws setup) :
    speedInMetersPerSecond
        (setup.swingSpeed .immediatelyAfterCollision) =
      Real.sqrt
        (2 * accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.maximumVerticalRise) := by
  have hTopSpeed :
      speedInMetersPerSecond (setup.swingSpeed .topOfSwing) = 0 := by
    simpa only [speedInMetersPerSecond] using
      hScenario.compositeStopsAtTopOfSwing
        LengthUnit.meters TimeUnit.seconds
  have hKineticAfter :
      2 * energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
          (setup.translationalKineticEnergy .immediatelyAfterCollision) =
        massInKilograms setup.compositeMass *
          speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision) ^ 2 := by
    simpa only [massInKilograms, speedInMetersPerSecond] using
      hEnergy.translationalKineticEnergyLaw
        SwingStage.immediatelyAfterCollision MassUnit.kilograms
          LengthUnit.meters TimeUnit.seconds
  have hKineticTop :
      2 * energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
          (setup.translationalKineticEnergy .topOfSwing) =
        massInKilograms setup.compositeMass *
          speedInMetersPerSecond (setup.swingSpeed .topOfSwing) ^ 2 := by
    simpa only [massInKilograms, speedInMetersPerSecond] using
      hEnergy.translationalKineticEnergyLaw
        SwingStage.topOfSwing MassUnit.kilograms
          LengthUnit.meters TimeUnit.seconds
  have hPotential :
      energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
            (setup.gravitationalPotentialEnergy .topOfSwing) -
          energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
            (setup.gravitationalPotentialEnergy .immediatelyAfterCollision) =
        massInKilograms setup.compositeMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.maximumVerticalRise := by
    simpa only [massInKilograms,
      accelerationInMetersPerSecondSquared, lengthInMeters] using
      hEnergy.gravitationalPotentialEnergyGain
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hMechanical :=
    hEnergy.mechanicalEnergyConservation
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hKineticTopZero :
      energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
          (setup.translationalKineticEnergy .topOfSwing) = 0 := by
    have hTwiceKineticTopZero :
        2 * energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
            (setup.translationalKineticEnergy .topOfSwing) = 0 := by
      calc
        2 * energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
              (setup.translationalKineticEnergy .topOfSwing) =
            massInKilograms setup.compositeMass *
              speedInMetersPerSecond (setup.swingSpeed .topOfSwing) ^ 2 :=
          hKineticTop
        _ = 0 := by rw [hTopSpeed]; ring
    linarith
  have hKineticAfterEqualsPotentialGain :
      energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
          (setup.translationalKineticEnergy .immediatelyAfterCollision) =
        energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
              (setup.gravitationalPotentialEnergy .topOfSwing) -
          energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
              (setup.gravitationalPotentialEnergy
                .immediatelyAfterCollision) := by
    linarith [hMechanical, hKineticTopZero]
  have hKineticAfterEqualsMgh :
      energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
          (setup.translationalKineticEnergy .immediatelyAfterCollision) =
        massInKilograms setup.compositeMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.maximumVerticalRise := by
    calc
      energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
            (setup.translationalKineticEnergy .immediatelyAfterCollision) =
          energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
                (setup.gravitationalPotentialEnergy .topOfSwing) -
            energyReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
                (setup.gravitationalPotentialEnergy
                  .immediatelyAfterCollision) :=
        hKineticAfterEqualsPotentialGain
      _ = massInKilograms setup.compositeMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.maximumVerticalRise :=
        hPotential
  have hScaledEnergy :
      massInKilograms setup.compositeMass *
          speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision) ^ 2 =
        massInKilograms setup.compositeMass *
          (2 * accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude *
              lengthInMeters setup.maximumVerticalRise) := by
    calc
      massInKilograms setup.compositeMass *
            speedInMetersPerSecond
              (setup.swingSpeed .immediatelyAfterCollision) ^ 2 =
          2 * energyReadout MassUnit.kilograms LengthUnit.meters
            TimeUnit.seconds
            (setup.translationalKineticEnergy
              .immediatelyAfterCollision) :=
        hKineticAfter.symm
      _ = 2 * (massInKilograms setup.compositeMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.maximumVerticalRise) := by
        rw [hKineticAfterEqualsMgh]
      _ = massInKilograms setup.compositeMass *
            (2 * accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                lengthInMeters setup.maximumVerticalRise) := by
        ring
  have hSpeedSquared :
      speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision) ^ 2 =
        2 * accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.maximumVerticalRise := by
    exact mul_left_cancel₀
      (ne_of_gt hPhysical.compositeMassPositive) hScaledEnergy
  have hRadicandNonnegative :
      0 ≤
        2 * accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.maximumVerticalRise := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (le_of_lt hPhysical.gravityPositive))
      hPhysical.maximumRiseNonnegative
  nlinarith [Real.sq_sqrt hRadicandNonnegative,
    Real.sqrt_nonneg
      (2 * accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.maximumVerticalRise),
    hPhysical.postImpactSpeedNonnegative]

/-!
Horizontal momentum conservation across the embedding collision gives the
mass-ratio relation between `v_1` and `v_2`.
-/
lemma bulletInitialSpeed_eq_massRatio_mul_postImpactSpeed
    (setup : BallisticPendulumSetup)
    (hScenario : MatchesStatedScenario setup)
    (hPhysical : HasPhysicalParameters setup)
    (hMomentum : SatisfiesStickingCollisionMomentumLaws setup) :
    speedInMetersPerSecond (setup.speedBeforeCollision .bullet) =
      ((massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) /
          massInKilograms (setup.bodyMass .bullet)) *
        speedInMetersPerSecond
          (setup.swingSpeed .immediatelyAfterCollision) := by
  have hBlockSpeed :
      speedInMetersPerSecond (setup.speedBeforeCollision .woodBlock) = 0 := by
    simpa only [speedInMetersPerSecond] using
      hScenario.woodenBlockInitiallyAtRest
        LengthUnit.meters TimeUnit.seconds
  have hCompositeMass :
      massInKilograms setup.compositeMass =
        massInKilograms (setup.bodyMass .bullet) +
          massInKilograms (setup.bodyMass .woodBlock) := by
    simpa only [massInKilograms] using
      hMomentum.compositeMassIsSum MassUnit.kilograms
  have hMomentumBefore :
      horizontalMomentumReadout MassUnit.kilograms
          LengthUnit.meters TimeUnit.seconds
          setup.horizontalMomentumBeforeCollision =
        massInKilograms (setup.bodyMass .bullet) *
            speedInMetersPerSecond (setup.speedBeforeCollision .bullet) +
          massInKilograms (setup.bodyMass .woodBlock) *
            speedInMetersPerSecond
              (setup.speedBeforeCollision .woodBlock) := by
    simpa only [massInKilograms, speedInMetersPerSecond] using
      hMomentum.momentumBeforeFactorization
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hMomentumAfter :
      horizontalMomentumReadout MassUnit.kilograms
          LengthUnit.meters TimeUnit.seconds
          setup.horizontalMomentumAfterCollision =
        massInKilograms setup.compositeMass *
          speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision) := by
    simpa only [massInKilograms, speedInMetersPerSecond] using
      hMomentum.momentumAfterFactorization
        MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hMomentumConservation :=
    hMomentum.horizontalMomentumConservation
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hMomentumBeforeReduced :
      horizontalMomentumReadout MassUnit.kilograms
          LengthUnit.meters TimeUnit.seconds
          setup.horizontalMomentumBeforeCollision =
        massInKilograms (setup.bodyMass .bullet) *
          speedInMetersPerSecond
            (setup.speedBeforeCollision .bullet) := by
    calc
      horizontalMomentumReadout MassUnit.kilograms
            LengthUnit.meters TimeUnit.seconds
            setup.horizontalMomentumBeforeCollision =
          massInKilograms (setup.bodyMass .bullet) *
              speedInMetersPerSecond
                (setup.speedBeforeCollision .bullet) +
            massInKilograms (setup.bodyMass .woodBlock) *
              speedInMetersPerSecond
                (setup.speedBeforeCollision .woodBlock) :=
        hMomentumBefore
      _ = massInKilograms (setup.bodyMass .bullet) *
            speedInMetersPerSecond
              (setup.speedBeforeCollision .bullet) := by
        rw [hBlockSpeed]
        ring
  have hMomentumAfterExpanded :
      horizontalMomentumReadout MassUnit.kilograms
          LengthUnit.meters TimeUnit.seconds
          setup.horizontalMomentumAfterCollision =
        (massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) *
          speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision) := by
    calc
      horizontalMomentumReadout MassUnit.kilograms
            LengthUnit.meters TimeUnit.seconds
            setup.horizontalMomentumAfterCollision =
          massInKilograms setup.compositeMass *
            speedInMetersPerSecond
              (setup.swingSpeed .immediatelyAfterCollision) :=
        hMomentumAfter
      _ = (massInKilograms (setup.bodyMass .bullet) +
              massInKilograms (setup.bodyMass .woodBlock)) *
            speedInMetersPerSecond
              (setup.swingSpeed .immediatelyAfterCollision) := by
        rw [hCompositeMass]
  have hBulletMomentum :
      massInKilograms (setup.bodyMass .bullet) *
          speedInMetersPerSecond (setup.speedBeforeCollision .bullet) =
        (massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) *
          speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision) := by
    calc
      massInKilograms (setup.bodyMass .bullet) *
            speedInMetersPerSecond
              (setup.speedBeforeCollision .bullet) =
          horizontalMomentumReadout MassUnit.kilograms
            LengthUnit.meters TimeUnit.seconds
            setup.horizontalMomentumBeforeCollision :=
        hMomentumBeforeReduced.symm
      _ = horizontalMomentumReadout MassUnit.kilograms
            LengthUnit.meters TimeUnit.seconds
            setup.horizontalMomentumAfterCollision :=
        hMomentumConservation
      _ = (massInKilograms (setup.bodyMass .bullet) +
              massInKilograms (setup.bodyMass .woodBlock)) *
            speedInMetersPerSecond
              (setup.swingSpeed .immediatelyAfterCollision) :=
        hMomentumAfterExpanded
  have hBulletMassNe :
      massInKilograms (setup.bodyMass .bullet) ≠ 0 :=
    ne_of_gt (hPhysical.eachBodyMassPositive .bullet)
  calc
    speedInMetersPerSecond (setup.speedBeforeCollision .bullet) =
        ((massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) *
          speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision)) /
          massInKilograms (setup.bodyMass .bullet) := by
      apply (eq_div_iff hBulletMassNe).2
      nlinarith [hBulletMomentum]
    _ = ((massInKilograms (setup.bodyMass .bullet) +
              massInKilograms (setup.bodyMass .woodBlock)) /
            massInKilograms (setup.bodyMass .bullet)) *
          speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision) := by
      ring

/-- Labels attached to the four formulas printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The speed expression printed beside each answer label, in metres per second. -/
def displayedInitialSpeedFormulaInMetersPerSecond
    (setup : BallisticPendulumSetup) : AnswerChoice → ℝ
  | .A =>
      ((massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) /
          massInKilograms (setup.bodyMass .bullet)) *
        Real.sqrt
          (accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.maximumVerticalRise)
  | .B =>
      ((massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) /
          massInKilograms (setup.bodyMass .bullet)) *
        Real.sqrt
          (2 * accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude *
              lengthInMeters setup.maximumVerticalRise)
  | .C =>
      ((massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) /
          massInKilograms (setup.bodyMass .woodBlock)) *
        Real.sqrt
          (2 * accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude *
              lengthInMeters setup.maximumVerticalRise)
  | .D =>
      ((massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) /
          massInKilograms (setup.bodyMass .woodBlock)) *
        Real.sqrt
          (accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.maximumVerticalRise)

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The initial bullet speed is

`v_1 = ((m_B + m_W) / m_B) * sqrt (2 g h)`,

which is the formula printed as answer B.  The exact relation is displayed
directly in the conclusion rather than hidden behind the answer-choice helper.

This formalizes blueprint label `thm:physics:phyx_mini_0815:target`.
-/
theorem problem_phyx_mini_0815
    (setup : BallisticPendulumSetup)
    (hScenario : MatchesStatedScenario setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hMomentum : SatisfiesStickingCollisionMomentumLaws setup)
    (hEnergy : SatisfiesConservativePendulumSwingLaws setup) :
    speedInMetersPerSecond (setup.speedBeforeCollision .bullet) =
      ((massInKilograms (setup.bodyMass .bullet) +
            massInKilograms (setup.bodyMass .woodBlock)) /
          massInKilograms (setup.bodyMass .bullet)) *
        Real.sqrt
          (2 * accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude *
              lengthInMeters setup.maximumVerticalRise) := by
  calc
    speedInMetersPerSecond (setup.speedBeforeCollision .bullet) =
        ((massInKilograms (setup.bodyMass .bullet) +
              massInKilograms (setup.bodyMass .woodBlock)) /
            massInKilograms (setup.bodyMass .bullet)) *
          speedInMetersPerSecond
            (setup.swingSpeed .immediatelyAfterCollision) :=
      bulletInitialSpeed_eq_massRatio_mul_postImpactSpeed
        setup hScenario hPhysical hMomentum
    _ = ((massInKilograms (setup.bodyMass .bullet) +
              massInKilograms (setup.bodyMass .woodBlock)) /
            massInKilograms (setup.bodyMass .bullet)) *
          Real.sqrt
            (2 * accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                lengthInMeters setup.maximumVerticalRise) := by
      rw [postImpactSpeed_eq_sqrt_two_g_h
        setup hScenario hPhysical hEnergy]

end PhyXMiniProblems.ProblemPhyXMini0815
