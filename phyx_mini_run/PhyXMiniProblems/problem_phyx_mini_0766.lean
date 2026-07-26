import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0766

open Dimension

/-!
# Stuntman swing, inelastic grapple, and frictional slide

An `80.0 kg` stuntman starts at rest and swings from a rope, lowering his
center of mass by `5.0 m`.  At the bottom he releases the rope and grapples
with a stationary `70.0 kg` villain.  The pair then slide together on a
horizontal floor whose coefficient of kinetic friction is `0.250`.

Masses, lengths, speeds, and accelerations below are unit-independent Physlib
quantities.  Real numbers are used only for named-unit readouts, the
dimensionless friction coefficient, and displayed answer values.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative speed magnitude, with dimension length per time. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative acceleration magnitude, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a speed in a coherent selected length-per-time unit. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read an acceleration in a coherent selected length-per-time-squared unit. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout for the two people. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout for the center-of-mass drop and the slide distance. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metres-per-second readout for all speeds in the one-dimensional model. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metres-per-second-squared readout for the gravitational acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Physical roles and primary-figure evidence -/

/-- The support to which the swing rope is attached in the problem statement. -/
inductive RopeSupport where
  | chandelier
  deriving DecidableEq, Repr

/-- The horizontal surface on which the grappled pair come to rest. -/
inductive FloorCondition where
  | horizontalWithKineticFriction
  deriving DecidableEq, Repr

/-- The physical outcome of the grapple at the bottom of the swing. -/
inductive CollisionOutcome where
  | grappleAndMoveTogether
  deriving DecidableEq, Repr

/-- The instant at which the stuntman lets go of the rope. -/
inductive RopeReleaseEvent where
  | atBottomImmediatelyBeforeGrapple
  deriving DecidableEq, Repr

/-- Direction of the dashed trajectory arrow in the supplied figure. -/
inductive SwingDirection where
  | downwardAndTowardVillain
  deriving DecidableEq, Repr

/-- Visual elements distinguished in the supplied one-panel figure. -/
inductive FigureFeature where
  | stuntman
  | villain
  | rope
  | chandelier
  | windowLedge
  | floor
  | dashedSwingArc
  | verticalDropMarker
  deriving DecidableEq, Fintype, Repr

/-!
Primary-image data.  The three printed numerical labels remain physical
quantities and are tied to the setup by `MatchesProblemAndFigure`; the image
contains no label for the requested slide distance.
-/
structure StuntSwingFigure where
  featureShown : FigureFeature → Bool
  stuntmanMassLabel : MassQuantity
  villainMassLabel : MassQuantity
  centerOfMassDropLabel : LengthQuantity
  trajectoryDirection : SwingDirection

/-! ## Setup, statement data, and governing laws -/

/-!
All independent quantities required by the three-stage model.  In particular,
`slideDistance` is unconstrained until the governing laws are supplied; no
field assigns it an answer-choice value.
-/
structure StuntGrappleSlideSetup where
  stuntmanMass : MassQuantity
  villainMass : MassQuantity
  centerOfMassDrop : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  kineticFrictionCoefficient : ℝ
  stuntmanInitialSpeed : SpeedQuantity
  stuntmanSpeedAtRelease : SpeedQuantity
  villainInitialSpeed : SpeedQuantity
  pairSpeedImmediatelyAfterGrapple : SpeedQuantity
  pairFinalSpeed : SpeedQuantity
  slideDistance : LengthQuantity
  ropeSupport : RopeSupport
  floorCondition : FloorCondition
  collisionOutcome : CollisionOutcome
  releaseEvent : RopeReleaseEvent
  figure : StuntSwingFigure

/-!
Numerical and qualitative data read from the prose and primary figure.  The
friction coefficient is dimensionless.  This predicate contains neither a
slide-distance value nor an answer-choice label.
-/
structure MatchesProblemAndFigure
    (setup : StuntGrappleSlideSetup) : Prop where
  stuntmanMassKilograms : massInKilograms setup.stuntmanMass = 80
  villainMassKilograms : massInKilograms setup.villainMass = 70
  centerOfMassDropMeters : lengthInMeters setup.centerOfMassDrop = 5
  kineticFrictionCoefficientValue : setup.kineticFrictionCoefficient = 1 / 4
  ropeAttachedToChandelier : setup.ropeSupport = .chandelier
  floorIsHorizontalAndResistive :
    setup.floorCondition = .horizontalWithKineticFriction
  pairMovesTogetherAfterGrapple :
    setup.collisionOutcome = .grappleAndMoveTogether
  releasesAtBottom :
    setup.releaseEvent = .atBottomImmediatelyBeforeGrapple
  figureShowsAllFeatures : ∀ feature, setup.figure.featureShown feature = true
  figureTrajectoryDirection :
    setup.figure.trajectoryDirection = .downwardAndTowardVillain
  figureStuntmanMassLabel :
    setup.figure.stuntmanMassLabel = setup.stuntmanMass
  figureVillainMassLabel :
    setup.figure.villainMassLabel = setup.villainMass
  figureDropLabel :
    setup.figure.centerOfMassDropLabel = setup.centerOfMassDrop

/-!
Initial and terminal boundary conditions stated or implied by “stands,” the
stationary villain, and “how far do they slide.”  These conditions do not
fix the requested distance.
-/
structure MatchesBoundaryConditions
    (setup : StuntGrappleSlideSetup) : Prop where
  stuntmanStartsAtRest :
    speedInMetersPerSecond setup.stuntmanInitialSpeed = 0
  villainStartsAtRest :
    speedInMetersPerSecond setup.villainInitialSpeed = 0
  pairAtRestAfterSliding :
    speedInMetersPerSecond setup.pairFinalSpeed = 0

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalParameters
    (setup : StuntGrappleSlideSetup) : Prop where
  stuntmanMassPositive : 0 < massInKilograms setup.stuntmanMass
  villainMassPositive : 0 < massInKilograms setup.villainMass
  centerOfMassDropPositive : 0 < lengthInMeters setup.centerOfMassDrop
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  kineticFrictionCoefficientPositive :
    0 < setup.kineticFrictionCoefficient

/-!
Conservation of mechanical energy from the ledge to rope release.  The
equation is multiplied by two and is stated for every coherent selection of
mass, length, and time units.  It relates the vertical center-of-mass drop to
the release speed without mentioning the later slide distance.
-/
structure SatisfiesSwingEnergyConservation
    (setup : StuntGrappleSlideSetup) : Prop where
  energyBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.stuntmanMass *
            speedReadout lengthUnit timeUnit setup.stuntmanInitialSpeed ^ 2 +
          2 * massReadout massUnit setup.stuntmanMass *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit setup.centerOfMassDrop =
        massReadout massUnit setup.stuntmanMass *
          speedReadout lengthUnit timeUnit setup.stuntmanSpeedAtRelease ^ 2

/-!
One-dimensional momentum conservation during the short perfectly inelastic
grapple.  Both incoming momentum terms are retained, and the outgoing mass is
the combined mass because the two people move together.
-/
structure SatisfiesGrappleMomentumConservation
    (setup : StuntGrappleSlideSetup) : Prop where
  momentumBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.stuntmanMass *
            speedReadout lengthUnit timeUnit setup.stuntmanSpeedAtRelease +
          massReadout massUnit setup.villainMass *
            speedReadout lengthUnit timeUnit setup.villainInitialSpeed =
        (massReadout massUnit setup.stuntmanMass +
            massReadout massUnit setup.villainMass) *
          speedReadout lengthUnit timeUnit
            setup.pairSpeedImmediatelyAfterGrapple

/-!
Work-energy balance during the horizontal slide.  On a horizontal floor the
normal-force magnitude is the combined weight, so the kinetic-friction work
has magnitude `mu_k * (m_stuntman + m_villain) * g * distance`.  Multiplying
the usual work-energy equation by two gives the relation below.  This is the
general friction law, not the requested numerical answer.
-/
structure SatisfiesFrictionWorkEnergyLaw
    (setup : StuntGrappleSlideSetup) : Prop where
  workEnergyBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      (massReadout massUnit setup.stuntmanMass +
          massReadout massUnit setup.villainMass) *
            speedReadout lengthUnit timeUnit
              setup.pairSpeedImmediatelyAfterGrapple ^ 2 =
        (massReadout massUnit setup.stuntmanMass +
            massReadout massUnit setup.villainMass) *
              speedReadout lengthUnit timeUnit setup.pairFinalSpeed ^ 2 +
          2 * setup.kineticFrictionCoefficient *
            (massReadout massUnit setup.stuntmanMass +
              massReadout massUnit setup.villainMass) *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration *
            lengthReadout lengthUnit setup.slideDistance

/-!
Eliminating both intermediate speeds and the gravitational acceleration gives
the generic mass-ratio relation.  This is derived from the three governing
laws and is not included in any premise structure.
-/
lemma slideDistance_massRatioRelation
    (setup : StuntGrappleSlideSetup)
    (_boundary : MatchesBoundaryConditions setup)
    (_physical : HasPhysicalParameters setup)
    (_swingEnergy : SatisfiesSwingEnergyConservation setup)
    (_grappleMomentum : SatisfiesGrappleMomentumConservation setup)
    (_frictionWork : SatisfiesFrictionWorkEnergyLaw setup) :
    setup.kineticFrictionCoefficient *
        (massInKilograms setup.stuntmanMass +
          massInKilograms setup.villainMass) ^ 2 *
        lengthInMeters setup.slideDistance =
      massInKilograms setup.stuntmanMass ^ 2 *
        lengthInMeters setup.centerOfMassDrop := by
  have hEnergy :
      massInKilograms setup.stuntmanMass *
            speedInMetersPerSecond setup.stuntmanInitialSpeed ^ 2 +
          2 * massInKilograms setup.stuntmanMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.centerOfMassDrop =
        massInKilograms setup.stuntmanMass *
          speedInMetersPerSecond setup.stuntmanSpeedAtRelease ^ 2 :=
    _swingEnergy.energyBalance
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hMomentum :
      massInKilograms setup.stuntmanMass *
            speedInMetersPerSecond setup.stuntmanSpeedAtRelease +
          massInKilograms setup.villainMass *
            speedInMetersPerSecond setup.villainInitialSpeed =
        (massInKilograms setup.stuntmanMass +
            massInKilograms setup.villainMass) *
          speedInMetersPerSecond
            setup.pairSpeedImmediatelyAfterGrapple :=
    _grappleMomentum.momentumBalance
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hFriction :
      (massInKilograms setup.stuntmanMass +
          massInKilograms setup.villainMass) *
            speedInMetersPerSecond
              setup.pairSpeedImmediatelyAfterGrapple ^ 2 =
        (massInKilograms setup.stuntmanMass +
            massInKilograms setup.villainMass) *
              speedInMetersPerSecond setup.pairFinalSpeed ^ 2 +
          2 * setup.kineticFrictionCoefficient *
            (massInKilograms setup.stuntmanMass +
              massInKilograms setup.villainMass) *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.slideDistance :=
    _frictionWork.workEnergyBalance
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hCombinedMassPositive :
      0 <
        massInKilograms setup.stuntmanMass +
          massInKilograms setup.villainMass :=
    add_pos _physical.stuntmanMassPositive _physical.villainMassPositive
  have hEnergyReduced :
      speedInMetersPerSecond setup.stuntmanSpeedAtRelease ^ 2 =
        2 *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.centerOfMassDrop := by
    apply mul_left_cancel₀ (ne_of_gt _physical.stuntmanMassPositive)
    calc
      massInKilograms setup.stuntmanMass *
            speedInMetersPerSecond setup.stuntmanSpeedAtRelease ^ 2 =
          massInKilograms setup.stuntmanMass *
              speedInMetersPerSecond setup.stuntmanInitialSpeed ^ 2 +
            2 * massInKilograms setup.stuntmanMass *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              lengthInMeters setup.centerOfMassDrop := hEnergy.symm
      _ = massInKilograms setup.stuntmanMass *
            (2 *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              lengthInMeters setup.centerOfMassDrop) := by
          rw [_boundary.stuntmanStartsAtRest]
          ring
  have hMomentumReduced :
      massInKilograms setup.stuntmanMass *
            speedInMetersPerSecond setup.stuntmanSpeedAtRelease =
        (massInKilograms setup.stuntmanMass +
            massInKilograms setup.villainMass) *
          speedInMetersPerSecond
            setup.pairSpeedImmediatelyAfterGrapple := by
    simpa only [_boundary.villainStartsAtRest, mul_zero, add_zero] using
      hMomentum
  have hMomentumSquared :
      massInKilograms setup.stuntmanMass ^ 2 *
            speedInMetersPerSecond setup.stuntmanSpeedAtRelease ^ 2 =
        (massInKilograms setup.stuntmanMass +
            massInKilograms setup.villainMass) ^ 2 *
          speedInMetersPerSecond
            setup.pairSpeedImmediatelyAfterGrapple ^ 2 := by
    calc
      massInKilograms setup.stuntmanMass ^ 2 *
            speedInMetersPerSecond setup.stuntmanSpeedAtRelease ^ 2 =
          (massInKilograms setup.stuntmanMass *
            speedInMetersPerSecond setup.stuntmanSpeedAtRelease) ^ 2 := by
              ring
      _ = ((massInKilograms setup.stuntmanMass +
              massInKilograms setup.villainMass) *
            speedInMetersPerSecond
              setup.pairSpeedImmediatelyAfterGrapple) ^ 2 := by
              rw [hMomentumReduced]
      _ = (massInKilograms setup.stuntmanMass +
              massInKilograms setup.villainMass) ^ 2 *
            speedInMetersPerSecond
              setup.pairSpeedImmediatelyAfterGrapple ^ 2 := by
              ring
  have hFrictionReduced :
      speedInMetersPerSecond
            setup.pairSpeedImmediatelyAfterGrapple ^ 2 =
        2 * setup.kineticFrictionCoefficient *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          lengthInMeters setup.slideDistance := by
    apply mul_left_cancel₀ (ne_of_gt hCombinedMassPositive)
    calc
      (massInKilograms setup.stuntmanMass +
            massInKilograms setup.villainMass) *
          speedInMetersPerSecond
            setup.pairSpeedImmediatelyAfterGrapple ^ 2 =
          (massInKilograms setup.stuntmanMass +
              massInKilograms setup.villainMass) *
                speedInMetersPerSecond setup.pairFinalSpeed ^ 2 +
            2 * setup.kineticFrictionCoefficient *
              (massInKilograms setup.stuntmanMass +
                massInKilograms setup.villainMass) *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              lengthInMeters setup.slideDistance := hFriction
      _ = (massInKilograms setup.stuntmanMass +
              massInKilograms setup.villainMass) *
            (2 * setup.kineticFrictionCoefficient *
              accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              lengthInMeters setup.slideDistance) := by
          rw [_boundary.pairAtRestAfterSliding]
          ring
  apply mul_left_cancel₀
    (mul_ne_zero (by norm_num)
      (ne_of_gt _physical.gravitationalAccelerationPositive) :
        2 *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration ≠ 0)
  calc
    (2 *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration) *
        (setup.kineticFrictionCoefficient *
          (massInKilograms setup.stuntmanMass +
            massInKilograms setup.villainMass) ^ 2 *
          lengthInMeters setup.slideDistance) =
        (massInKilograms setup.stuntmanMass +
            massInKilograms setup.villainMass) ^ 2 *
          (2 * setup.kineticFrictionCoefficient *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.slideDistance) := by
      ring
    _ = (massInKilograms setup.stuntmanMass +
            massInKilograms setup.villainMass) ^ 2 *
          speedInMetersPerSecond
            setup.pairSpeedImmediatelyAfterGrapple ^ 2 := by
      rw [hFrictionReduced]
    _ = massInKilograms setup.stuntmanMass ^ 2 *
          speedInMetersPerSecond setup.stuntmanSpeedAtRelease ^ 2 := by
      rw [hMomentumSquared]
    _ = massInKilograms setup.stuntmanMass ^ 2 *
          (2 *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.centerOfMassDrop) := by
      rw [hEnergyReduced]
    _ = (2 *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration) *
        (massInKilograms setup.stuntmanMass ^ 2 *
          lengthInMeters setup.centerOfMassDrop) := by
      ring

/-! ## Displayed answers and final target -/

/-- Labels attached to the four distances printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metres printed beside each displayed answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 46 / 10
  | .B => 57 / 10
  | .C => 42 / 10
  | .D => 48 / 10

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- Agreement with a displayed distance after rounding to the nearest tenth metre. -/
def MatchesAnswerChoice
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters distance - choice.meters| < (1 / 20 : ℝ)

/-!
The three-stage calculation gives the exact distance

`((80 / (80 + 70))^2 * 5) / 0.250 = 256/45 m`,

which rounds to `5.7 m`, displayed answer B.  Neither the exact value nor
choice B occurs in any theorem premise.

This formalizes blueprint label `thm:physics:phyx_mini_0766:target`.
-/
theorem slideDistance_matches_recordedAnswerB
    (setup : StuntGrappleSlideSetup)
    (_problem : MatchesProblemAndFigure setup)
    (_boundary : MatchesBoundaryConditions setup)
    (_physical : HasPhysicalParameters setup)
    (_swingEnergy : SatisfiesSwingEnergyConservation setup)
    (_grappleMomentum : SatisfiesGrappleMomentumConservation setup)
    (_frictionWork : SatisfiesFrictionWorkEnergyLaw setup) :
    lengthInMeters setup.slideDistance = 256 / 45 ∧
      MatchesAnswerChoice setup.slideDistance recordedAnswerChoice := by
  have hMassRatio :=
    slideDistance_massRatioRelation setup _boundary _physical
      _swingEnergy _grappleMomentum _frictionWork
  have hDistance : lengthInMeters setup.slideDistance = 256 / 45 := by
    rw [_problem.kineticFrictionCoefficientValue,
      _problem.stuntmanMassKilograms,
      _problem.villainMassKilograms,
      _problem.centerOfMassDropMeters] at hMassRatio
    norm_num at hMassRatio ⊢
    linarith
  constructor
  · exact hDistance
  · simp only [MatchesAnswerChoice, recordedAnswerChoice,
      AnswerChoice.meters, hDistance]
    norm_num [abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0766
