import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Two equal masses colliding in a hemispherical bowl

This file formalizes problem `phyx_mini_0767`.  One mass starts from rest at
the left rim of a smooth hemispherical bowl, while an identical mass starts
from rest at the bottom.  The first mass descends, the masses stick in their
collision at the bottom, and the compound body subsequently rises in the
bowl.

Lengths, masses, acceleration magnitudes, and signed tangential velocities
are unit-independent Physlib quantities.  Scalar equations below are readouts
in an arbitrary coherent choice of units.  The positive tangential direction
at the collision is chosen to be the incoming direction of the rim mass.

Assumption/target boundary:

* `MatchesBowlCollisionScenario` records the qualitative mechanical model;
* `MatchesSuppliedFigure` records the two pictured locations and the label
  `R`;
* `MatchesInitialAndCollisionGeometry` records equal masses, release from
  rest, and the rim/bottom height data;
* `SatisfiesBowlCollisionConservationLaws` states the generic energy and
  tangential-momentum laws; and
* the maximum rise `R / 4` and answer choice B occur only in conclusions.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0767

open Dimension

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude with physical dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-!
A signed tangential velocity.  The real carrier retains the sign needed by
the one-dimensional momentum balance, while `WithDim` retains dimension
`L T⁻¹`.
-/
abbrev TangentialVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Scalar readout of a physical length in a coherent choice of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Scalar readout of a physical mass in a coherent choice of units. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  ((mass units).val : ℝ)

/-- Scalar readout of an acceleration magnitude in coherent units. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration units).val : ℝ)

/-- Scalar readout of a signed tangential velocity in coherent units. -/
def tangentialVelocityReadout
    (units : UnitChoices) (velocity : TangentialVelocityQuantity) : ℝ :=
  (velocity units).val

/-!
The scalar readout of `m g h`.  Its factors are dimension-tagged quantities,
so this helper is an energy readout rather than an untyped physical primitive.
-/
def gravitationalPotentialEnergyReadout
    (units : UnitChoices) (mass : MassQuantity)
    (gravity : AccelerationMagnitudeQuantity) (height : LengthQuantity) : ℝ :=
  massReadout units mass * accelerationReadout units gravity *
    lengthReadout units height

/-- The scalar readout of the translational kinetic energy `m v² / 2`. -/
def translationalKineticEnergyReadout
    (units : UnitChoices) (mass : MassQuantity)
    (velocity : TangentialVelocityQuantity) : ℝ :=
  (1 / 2 : ℝ) * massReadout units mass *
    tangentialVelocityReadout units velocity ^ 2

/-- The signed one-dimensional tangential momentum readout `m v`. -/
def tangentialMomentumReadout
    (units : UnitChoices) (mass : MassQuantity)
    (velocity : TangentialVelocityQuantity) : ℝ :=
  massReadout units mass * tangentialVelocityReadout units velocity

/-! ## Bodies, apparatus, and primary-figure vocabulary -/

/-- The two identical bodies distinguished by their pictured starting places. -/
inductive BowlMass where
  | rim
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- Distinguished locations in the lower semicircular cross-section. -/
inductive BowlLocation where
  | leftRim
  | bottom
  | other
  deriving DecidableEq, Repr

/-- Geometric model of the confining bowl. -/
inductive BowlGeometry where
  | hemispherical
  | other
  deriving DecidableEq, Repr

/-- Contact condition between each mass and the bowl surface. -/
inductive SurfaceCondition where
  | smoothFrictionless
  | rough
  deriving DecidableEq, Repr

/-- Mechanical behavior of the two bodies at impact. -/
inductive CollisionBehavior where
  | stickTogether
  | rebound
  deriving DecidableEq, Repr

/-- The literal symbolic label visible beside the radius segment. -/
inductive FigureLabel where
  | capitalR
  deriving DecidableEq, Repr

/-!
Qualitative information in the primary raster `phyx_data/test_image/767.png`.
The image is a lower semicircular cross-section with one square at the left
rim, one at the bottom, and a center-to-wall segment marked `R`.
-/
structure HemisphericalBowlFigure where
  massShown : BowlMass → Bool
  depictedInitialLocation : BowlMass → BowlLocation
  lowerSemicircleShown : Bool
  radiusSegmentShown : Bool
  radiusSegmentStartsAtCenter : Bool
  radiusSegmentEndsOnBowl : Bool
  radiusSegmentLabel : FigureLabel

/-!
Independent physical quantities for the experiment.  In particular,
`maximumRiseHeight` is an unconstrained observable; it is not defined from
the radius or from an answer choice.
-/
structure BowlCollisionSetup where
  geometry : BowlGeometry
  surfaceCondition : SurfaceCondition
  collisionBehavior : CollisionBehavior
  collisionLocation : BowlLocation
  bowlRadius : LengthQuantity
  bodyMass : BowlMass → MassQuantity
  gravitationalAcceleration : AccelerationMagnitudeQuantity
  initialHeightAboveBottom : BowlMass → LengthQuantity
  collisionHeightAboveBottom : LengthQuantity
  initialTangentialVelocity : BowlMass → TangentialVelocityQuantity
  tangentialVelocityImmediatelyBeforeCollision :
    BowlMass → TangentialVelocityQuantity
  commonTangentialVelocityImmediatelyAfterCollision :
    TangentialVelocityQuantity
  tangentialVelocityAtMaximumHeight : TangentialVelocityQuantity
  maximumRiseHeight : LengthQuantity
  figure : HemisphericalBowlFigure

/-! ## Scenario, figure readouts, and supplied initial data -/

/-- The qualitative assumptions stated in the problem prose. -/
structure MatchesBowlCollisionScenario
    (setup : BowlCollisionSetup) : Prop where
  bowlIsHemispherical : setup.geometry = .hemispherical
  bowlIsSmoothAndFrictionless :
    setup.surfaceCondition = .smoothFrictionless
  bodiesStickAtImpact : setup.collisionBehavior = .stickTogether
  impactOccursAtBottom : setup.collisionLocation = .bottom

/-- Facts read directly from the supplied primary figure. -/
structure MatchesSuppliedFigure
    (setup : BowlCollisionSetup) : Prop where
  bothMassesShown : ∀ body, setup.figure.massShown body = true
  rimMassAtLeftRim :
    setup.figure.depictedInitialLocation .rim = .leftRim
  bottomMassAtBottom :
    setup.figure.depictedInitialLocation .bottom = .bottom
  lowerSemicircleVisible : setup.figure.lowerSemicircleShown = true
  radiusSegmentVisible : setup.figure.radiusSegmentShown = true
  radiusStartsAtCenter :
    setup.figure.radiusSegmentStartsAtCenter = true
  radiusEndsOnBowl : setup.figure.radiusSegmentEndsOnBowl = true
  radiusIsMarkedR : setup.figure.radiusSegmentLabel = .capitalR

/-!
Quantitative geometry and initial conditions supplied by the prose and image.
The left-rim height equals the radius, the other mass and the collision are
at the zero-height bottom, both bodies are released from rest, and their
physical masses are equal.  No post-collision speed or rise height is fixed.
-/
structure MatchesInitialAndCollisionGeometry
    (setup : BowlCollisionSetup) : Prop where
  massesAreIdentical :
    setup.bodyMass .rim = setup.bodyMass .bottom
  rimInitialHeightEqualsRadius :
    setup.initialHeightAboveBottom .rim = setup.bowlRadius
  bottomInitialHeightIsZero : ∀ units,
    lengthReadout units (setup.initialHeightAboveBottom .bottom) = 0
  collisionHeightIsZero : ∀ units,
    lengthReadout units setup.collisionHeightAboveBottom = 0
  releasedFromRest : ∀ body units,
    tangentialVelocityReadout units
      (setup.initialTangentialVelocity body) = 0

/-! Positivity and orientation conditions selecting the physical branch. -/
structure HasPhysicalBowlParameters
    (setup : BowlCollisionSetup) : Prop where
  radiusPositive :
    0 < lengthReadout UnitChoices.SI setup.bowlRadius
  massPositive : ∀ body,
    0 < massReadout UnitChoices.SI (setup.bodyMass body)
  gravitationalAccelerationPositive :
    0 < accelerationReadout UnitChoices.SI
      setup.gravitationalAcceleration
  rimMassApproachesInPositiveDirection :
    0 ≤ tangentialVelocityReadout UnitChoices.SI
      (setup.tangentialVelocityImmediatelyBeforeCollision .rim)
  compoundBodyLeavesInPositiveDirection :
    0 ≤ tangentialVelocityReadout UnitChoices.SI
      setup.commonTangentialVelocityImmediatelyAfterCollision

/-! ## Governing mechanical laws -/

/-!
The generic mechanical laws used in the textbook solution:

* mechanical energy of the rim mass is conserved during its frictionless
  descent;
* the mass initially at the bottom remains at rest until impact;
* tangential momentum is conserved during the short sticking collision; and
* mechanical energy of the joined body is conserved from just after impact
  to its zero-speed turning point.

These laws quantify over every coherent unit choice.  They contain no
specialized value for the maximum height and no answer-choice fraction.
-/
structure SatisfiesBowlCollisionConservationLaws
    (setup : BowlCollisionSetup) : Prop where
  frictionlessDescentEnergyConservation : ∀ units,
    gravitationalPotentialEnergyReadout units
          (setup.bodyMass .rim) setup.gravitationalAcceleration
          (setup.initialHeightAboveBottom .rim) +
        translationalKineticEnergyReadout units
          (setup.bodyMass .rim) (setup.initialTangentialVelocity .rim) =
      gravitationalPotentialEnergyReadout units
          (setup.bodyMass .rim) setup.gravitationalAcceleration
          setup.collisionHeightAboveBottom +
        translationalKineticEnergyReadout units
          (setup.bodyMass .rim)
          (setup.tangentialVelocityImmediatelyBeforeCollision .rim)
  bottomMassRemainsAtRestUntilCollision : ∀ units,
    tangentialVelocityReadout units
        (setup.tangentialVelocityImmediatelyBeforeCollision .bottom) =
      tangentialVelocityReadout units
        (setup.initialTangentialVelocity .bottom)
  stickingCollisionTangentialMomentumConservation : ∀ units,
    tangentialMomentumReadout units
          (setup.bodyMass .rim)
          (setup.tangentialVelocityImmediatelyBeforeCollision .rim) +
        tangentialMomentumReadout units
          (setup.bodyMass .bottom)
          (setup.tangentialVelocityImmediatelyBeforeCollision .bottom) =
      (massReadout units (setup.bodyMass .rim) +
          massReadout units (setup.bodyMass .bottom)) *
        tangentialVelocityReadout units
          setup.commonTangentialVelocityImmediatelyAfterCollision
  compoundBodyAscentEnergyConservation : ∀ units,
    (massReadout units (setup.bodyMass .rim) +
          massReadout units (setup.bodyMass .bottom)) *
          accelerationReadout units setup.gravitationalAcceleration *
          lengthReadout units setup.collisionHeightAboveBottom +
        (1 / 2 : ℝ) *
          (massReadout units (setup.bodyMass .rim) +
            massReadout units (setup.bodyMass .bottom)) *
          tangentialVelocityReadout units
              setup.commonTangentialVelocityImmediatelyAfterCollision ^ 2 =
      (massReadout units (setup.bodyMass .rim) +
          massReadout units (setup.bodyMass .bottom)) *
          accelerationReadout units setup.gravitationalAcceleration *
          lengthReadout units setup.maximumRiseHeight +
        (1 / 2 : ℝ) *
          (massReadout units (setup.bodyMass .rim) +
            massReadout units (setup.bodyMass .bottom)) *
          tangentialVelocityReadout units
              setup.tangentialVelocityAtMaximumHeight ^ 2
  maximumHeightIsTurningPoint : ∀ units,
    tangentialVelocityReadout units
      setup.tangentialVelocityAtMaximumHeight = 0

/-! ## Derived relations along the solution route -/

/-!
Frictionless descent from the rim to the bottom gives
`v_impact² = 2 g R`.
-/
lemma rim_impact_velocity_squared
    (setup : BowlCollisionSetup)
    (hData : MatchesInitialAndCollisionGeometry setup)
    (hPhysical : HasPhysicalBowlParameters setup)
    (hLaws : SatisfiesBowlCollisionConservationLaws setup) :
    ∀ units,
      tangentialVelocityReadout units
          (setup.tangentialVelocityImmediatelyBeforeCollision .rim) ^ 2 =
        2 * accelerationReadout units setup.gravitationalAcceleration *
          lengthReadout units setup.bowlRadius := by
  intro units
  have hEnergy :=
    hLaws.frictionlessDescentEnergyConservation units
  rw [hData.rimInitialHeightEqualsRadius] at hEnergy
  simp only [gravitationalPotentialEnergyReadout,
    translationalKineticEnergyReadout,
    hData.releasedFromRest .rim units,
    hData.collisionHeightIsZero units] at hEnergy
  have hMassScale :=
    congrArg
      (fun x : WithDim M𝓭 NNReal => ((x.val : NNReal) : ℝ))
      ((setup.bodyMass .rim).property UnitChoices.SI units)
  change
    massReadout units (setup.bodyMass .rim) =
      (UnitChoices.dimScale UnitChoices.SI units M𝓭 : ℝ) *
        massReadout UnitChoices.SI (setup.bodyMass .rim)
    at hMassScale
  have hMass :
      0 < massReadout units (setup.bodyMass .rim) := by
    rw [hMassScale]
    exact mul_pos
      (by exact_mod_cast
        UnitChoices.dimScale_pos UnitChoices.SI units M𝓭)
      (hPhysical.massPositive .rim)
  apply mul_left_cancel₀ (ne_of_gt hMass)
  nlinarith [hEnergy]

/-!
For two equal masses, with the bottom mass initially stationary, tangential
momentum conservation makes the shared post-impact velocity half the incoming
rim-mass velocity.
-/
lemma common_velocity_after_sticking_is_half
    (setup : BowlCollisionSetup)
    (hData : MatchesInitialAndCollisionGeometry setup)
    (hPhysical : HasPhysicalBowlParameters setup)
    (hLaws : SatisfiesBowlCollisionConservationLaws setup) :
    ∀ units,
      tangentialVelocityReadout units
          setup.commonTangentialVelocityImmediatelyAfterCollision =
        tangentialVelocityReadout units
          (setup.tangentialVelocityImmediatelyBeforeCollision .rim) / 2 := by
  intro units
  have hBottom :=
    hLaws.bottomMassRemainsAtRestUntilCollision units
  rw [hData.releasedFromRest .bottom units] at hBottom
  have hMomentum :=
    hLaws.stickingCollisionTangentialMomentumConservation units
  simp only [tangentialMomentumReadout] at hMomentum
  rw [hBottom, ← hData.massesAreIdentical] at hMomentum
  have hMassScale :=
    congrArg
      (fun x : WithDim M𝓭 NNReal => ((x.val : NNReal) : ℝ))
      ((setup.bodyMass .rim).property UnitChoices.SI units)
  change
    massReadout units (setup.bodyMass .rim) =
      (UnitChoices.dimScale UnitChoices.SI units M𝓭 : ℝ) *
        massReadout UnitChoices.SI (setup.bodyMass .rim)
    at hMassScale
  have hMass :
      0 < massReadout units (setup.bodyMass .rim) := by
    rw [hMassScale]
    exact mul_pos
      (by exact_mod_cast
        UnitChoices.dimScale_pos UnitChoices.SI units M𝓭)
      (hPhysical.massPositive .rim)
  apply mul_left_cancel₀ (ne_of_gt hMass)
  nlinarith [hMomentum]

/-! ## Displayed choices and current target -/

/-- Labels printed beside the four candidate heights. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless coefficient of the bowl radius printed by each choice. -/
def AnswerChoice.radiusFraction : AnswerChoice → ℝ
  | .A => 1 / 3
  | .B => 1 / 4
  | .C => 1 / 2
  | .D => 1 / 5

/-- A choice is correct when its radius fraction equals the physical rise. -/
def IsCorrectAnswer
    (setup : BowlCollisionSetup) (choice : AnswerChoice) : Prop :=
  ∀ units,
    lengthReadout units setup.maximumRiseHeight =
      choice.radiusFraction * lengthReadout units setup.bowlRadius

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
After the sticking collision, the compound body rises one quarter of the
bowl radius above the bottom.  This is answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0767:target`.
-/
theorem problem_phyx_mini_0767
    (setup : BowlCollisionSetup)
    (hScenario : MatchesBowlCollisionScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hData : MatchesInitialAndCollisionGeometry setup)
    (hPhysical : HasPhysicalBowlParameters setup)
    (hLaws : SatisfiesBowlCollisionConservationLaws setup) :
    (∀ units,
      lengthReadout units setup.maximumRiseHeight =
        lengthReadout units setup.bowlRadius / 4) ∧
      IsCorrectAnswer setup recordedAnswerChoice := by
  have hRise :
      ∀ units,
        lengthReadout units setup.maximumRiseHeight =
          lengthReadout units setup.bowlRadius / 4 := by
    intro units
    have hImpact :=
      rim_impact_velocity_squared setup hData hPhysical hLaws units
    have hCommon :=
      common_velocity_after_sticking_is_half
        setup hData hPhysical hLaws units
    have hAscent :=
      hLaws.compoundBodyAscentEnergyConservation units
    rw [hData.collisionHeightIsZero units,
      hLaws.maximumHeightIsTurningPoint units,
      ← hData.massesAreIdentical] at hAscent
    have hMassScale :=
      congrArg
        (fun x : WithDim M𝓭 NNReal => ((x.val : NNReal) : ℝ))
        ((setup.bodyMass .rim).property UnitChoices.SI units)
    change
      massReadout units (setup.bodyMass .rim) =
        (UnitChoices.dimScale UnitChoices.SI units M𝓭 : ℝ) *
          massReadout UnitChoices.SI (setup.bodyMass .rim)
      at hMassScale
    have hMass :
        0 < massReadout units (setup.bodyMass .rim) := by
      rw [hMassScale]
      exact mul_pos
        (by exact_mod_cast
          UnitChoices.dimScale_pos UnitChoices.SI units M𝓭)
        (hPhysical.massPositive .rim)
    have hClimb :
        tangentialVelocityReadout units
              setup.commonTangentialVelocityImmediatelyAfterCollision ^ 2 =
          2 * accelerationReadout units setup.gravitationalAcceleration *
            lengthReadout units setup.maximumRiseHeight := by
      apply mul_left_cancel₀ (ne_of_gt (add_pos hMass hMass))
      nlinarith [hAscent]
    have hGravityScale :=
      congrArg
        (fun x :
          WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal =>
            ((x.val : NNReal) : ℝ))
        (setup.gravitationalAcceleration.property UnitChoices.SI units)
    change
      accelerationReadout units setup.gravitationalAcceleration =
        (UnitChoices.dimScale UnitChoices.SI units
            (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) : ℝ) *
          accelerationReadout UnitChoices.SI
            setup.gravitationalAcceleration
      at hGravityScale
    have hGravity :
        0 < accelerationReadout units
          setup.gravitationalAcceleration := by
      rw [hGravityScale]
      have hScalePositive :=
        UnitChoices.dimScale_pos UnitChoices.SI units
          (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹)
      exact mul_pos
        (by exact_mod_cast hScalePositive)
        hPhysical.gravitationalAccelerationPositive
    apply mul_left_cancel₀ (ne_of_gt hGravity)
    rw [hCommon] at hClimb
    nlinarith [hImpact, hClimb]
  refine ⟨hRise, ?_⟩
  intro units
  simpa [IsCorrectAnswer, recordedAnswerChoice,
    AnswerChoice.radiusFraction, div_eq_mul_inv, mul_comm] using hRise units

end PhyXMiniProblems.ProblemPhyXMini0767
