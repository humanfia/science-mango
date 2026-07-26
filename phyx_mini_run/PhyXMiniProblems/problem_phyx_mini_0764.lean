import Mathlib
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Momentum
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0764

open Dimension

/-!
# Sticking ice chunks ascending a frictionless valley

A `5.00 kg` chunk of ice travels rightward at `12.0 m/s` along the flat
floor of an icy valley. It collides with an identical stationary chunk and
the two chunks stick. The compound object then ascends the curved,
frictionless right side of the valley until it is instantaneously at rest.

The collision is modeled by conservation of horizontal linear momentum; its
kinetic energy is not assumed conserved. The subsequent ascent is modeled by
conservation of mechanical energy. Physical quantities are represented by
Physlib's unit-independent dimensionful types; real numbers occur only in
coherent-unit readouts, figure labels, and answer-choice data.

The source dataset records B (`1.2 m`). The pictured data and standard
terrestrial gravity instead imply an exact rise of `90/49 m`, approximately
`1.84 m`, for which C (`1.9 m`) is the unique closest listed value. The
recorded label is retained only as metadata and is not a physical premise.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- Gravitational acceleration has dimension length divided by time squared. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent height above the valley floor. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- Unit-independent one-dimensional momentum; rightward is positive. -/
abbrev MomentumQuantity : Type := Dimensionful (Momentum 1)

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

/-- Read signed momentum in coherent selected mechanical units. -/
def momentumReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (momentum : MomentumQuantity) : ℝ :=
  (momentum {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val 0

/-- Read energy in the coherent unit induced by selected base units. -/
def energyReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (energy : EnergyQuantity) : ℝ :=
  (energy {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metre-per-second readout of a speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-! ## Physical stages and primary-figure vocabulary -/

/-- The two separate chunks present immediately before the collision. -/
inductive IceChunk where
  | initiallyMoving
  | initiallyStationary
  deriving DecidableEq, Fintype, Repr

/-- The two states of the stuck pair during its frictionless ascent. -/
inductive AscentStage where
  | valleyFloorImmediatelyAfterCollision
  | highestPoint
  deriving DecidableEq, Fintype, Repr

/-- Qualitative direction of motion along the valley floor. -/
inductive HorizontalDirection where
  | rightward
  | leftward
  deriving DecidableEq, Repr

/-- Outcome of the short collision. -/
inductive CollisionOutcome where
  | chunksStickTogether
  | chunksSeparate
  deriving DecidableEq, Repr

/-- Idealization of the ice-covered floor and curved valley side. -/
inductive SurfaceCondition where
  | frictionlessIce
  | dissipativeSurface
  deriving DecidableEq, Repr

/-- Visible terrain regions distinguished in image `764.png`. -/
inductive TerrainRegion where
  | flatValleyFloor
  | curvedRisingRightSide
  deriving DecidableEq, Fintype, Repr

/-- Physical and graphical objects visible in image `764.png`. -/
inductive FigureObject where
  | movingIceChunk
  | stationaryIceChunk
  | movingChunkVelocityArrow
  | flatFloor
  | curvedHill
  deriving DecidableEq, Fintype, Repr

/-!
Literal evidence from the supplied raster. Its real-valued fields transcribe
printed labels only; `MatchesSuppliedFigure` connects those labels to the
independent dimensionful quantities in the physical setup.
-/
structure SuppliedIceValleyFigure where
  showsObject : FigureObject → Bool
  showsChunk : IceChunk → Bool
  massLabelKilograms : IceChunk → ℝ
  showsVelocityArrow : IceChunk → Bool
  velocityArrowDirection : HorizontalDirection
  velocityLabelMetersPerSecond : ℝ
  showsTerrainRegion : TerrainRegion → Bool
  floorJoinsRisingRightSide : Bool
  showsNumericalMaximumHeight : Bool

/-!
Independent physical quantities for the collision and ascent. In particular,
`maximumRiseAboveValleyFloor` is not defined from an answer choice and is
constrained only by the governing laws.
-/
structure IceValleyCollisionSetup where
  figure : SuppliedIceValleyFigure
  surfaceCondition : SurfaceCondition
  collisionOutcome : CollisionOutcome
  initialMotionDirection : HorizontalDirection
  postCollisionMotionDirection : HorizontalDirection
  chunkMass : IceChunk → MassQuantity
  initialSpeed : IceChunk → SpeedQuantity
  combinedMass : MassQuantity
  ascentSpeed : AscentStage → SpeedQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  maximumRiseAboveValleyFloor : LengthQuantity
  horizontalMomentumBeforeCollision : MomentumQuantity
  horizontalMomentumAfterCollision : MomentumQuantity
  translationalKineticEnergy : AscentStage → EnergyQuantity
  gravitationalPotentialEnergy : AscentStage → EnergyQuantity

/-! ## Scenario assignments, figure readouts, and governing laws -/

/-- Qualitative conditions and boundary states stated or implied by the problem. -/
structure MatchesIceValleyScenario
    (setup : IceValleyCollisionSetup) : Prop where
  surfaceIsFrictionless : setup.surfaceCondition = .frictionlessIce
  collisionIsPerfectlyInelastic :
    setup.collisionOutcome = .chunksStickTogether
  movingChunkTravelsRight : setup.initialMotionDirection = .rightward
  compoundObjectTravelsRight :
    setup.postCollisionMotionDirection = .rightward
  secondChunkInitiallyAtRest :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit
        (setup.initialSpeed .initiallyStationary) = 0
  compoundStopsAtHighestPoint :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit
        (setup.ascentSpeed .highestPoint) = 0

/-!
The masses and initial speed printed in the problem. No post-collision speed,
maximum height, or answer choice occurs in these data.
-/
structure MatchesProblemReadouts
    (setup : IceValleyCollisionSetup) : Prop where
  movingChunkMassKilograms :
    massInKilograms (setup.chunkMass .initiallyMoving) = 5
  stationaryChunkMassKilograms :
    massInKilograms (setup.chunkMass .initiallyStationary) = 5
  movingChunkInitialSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.initialSpeed .initiallyMoving) = 12

/-- Conventional near-Earth gravitational calibration for the numerical result. -/
structure UsesStandardTerrestrialGravity
    (setup : IceValleyCollisionSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude = 49 / 5

/-!
Primary-raster evidence: two `5.00 kg` blocks lie on the flat floor, only the
left block has a rightward `12.0 m/s` arrow, and the floor becomes a curved
rising right side. The image contains no maximum-height readout.
-/
structure MatchesSuppliedFigure
    (setup : IceValleyCollisionSetup) : Prop where
  everyFigureObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  bothChunksShown :
    ∀ chunk : IceChunk, setup.figure.showsChunk chunk = true
  movingChunkMassLabel :
    setup.figure.massLabelKilograms .initiallyMoving = 5
  stationaryChunkMassLabel :
    setup.figure.massLabelKilograms .initiallyStationary = 5
  movingChunkHasArrow :
    setup.figure.showsVelocityArrow .initiallyMoving = true
  stationaryChunkHasNoArrow :
    setup.figure.showsVelocityArrow .initiallyStationary = false
  arrowPointsRight : setup.figure.velocityArrowDirection = .rightward
  arrowLabel : setup.figure.velocityLabelMetersPerSecond = 12
  bothTerrainRegionsShown :
    ∀ region : TerrainRegion, setup.figure.showsTerrainRegion region = true
  floorTransitionsToHill : setup.figure.floorJoinsRisingRightSide = true
  noHeightReadout : setup.figure.showsNumericalMaximumHeight = false
  movingMassMatchesLabel :
    massInKilograms (setup.chunkMass .initiallyMoving) =
      setup.figure.massLabelKilograms .initiallyMoving
  stationaryMassMatchesLabel :
    massInKilograms (setup.chunkMass .initiallyStationary) =
      setup.figure.massLabelKilograms .initiallyStationary
  movingSpeedMatchesLabel :
    speedInMetersPerSecond (setup.initialSpeed .initiallyMoving) =
      setup.figure.velocityLabelMetersPerSecond

/-- Positivity and nondegeneracy conditions for the physical model. -/
structure HasPhysicalIceValleyParameters
    (setup : IceValleyCollisionSetup) : Prop where
  eachChunkMassPositive :
    ∀ chunk : IceChunk, 0 < massInKilograms (setup.chunkMass chunk)
  combinedMassPositive : 0 < massInKilograms setup.combinedMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  movingChunkSpeedPositive :
    0 < speedInMetersPerSecond (setup.initialSpeed .initiallyMoving)
  postCollisionSpeedPositive :
    0 < speedInMetersPerSecond
      (setup.ascentSpeed .valleyFloorImmediatelyAfterCollision)
  maximumRiseNonnegative :
    0 ≤ lengthInMeters setup.maximumRiseAboveValleyFloor

/-!
Mass additivity and one-dimensional linear-momentum conservation for the
short sticking collision. Speeds serve as signed components because the
scenario states that every nonzero horizontal motion is rightward. No field
assigns a numerical post-collision speed or height.
-/
structure SatisfiesStickingCollisionMomentumLaws
    (setup : IceValleyCollisionSetup) : Prop where
  compoundMassIsSum :
    ∀ massUnit : MassUnit,
      massReadout massUnit setup.combinedMass =
        massReadout massUnit (setup.chunkMass .initiallyMoving) +
          massReadout massUnit (setup.chunkMass .initiallyStationary)
  momentumBeforeFactorization :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      momentumReadout massUnit lengthUnit timeUnit
          setup.horizontalMomentumBeforeCollision =
        massReadout massUnit (setup.chunkMass .initiallyMoving) *
            speedReadout lengthUnit timeUnit
              (setup.initialSpeed .initiallyMoving) +
          massReadout massUnit (setup.chunkMass .initiallyStationary) *
            speedReadout lengthUnit timeUnit
              (setup.initialSpeed .initiallyStationary)
  momentumAfterFactorization :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      momentumReadout massUnit lengthUnit timeUnit
          setup.horizontalMomentumAfterCollision =
        massReadout massUnit setup.combinedMass *
          speedReadout lengthUnit timeUnit
            (setup.ascentSpeed .valleyFloorImmediatelyAfterCollision)
  horizontalMomentumConservation :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      momentumReadout massUnit lengthUnit timeUnit
          setup.horizontalMomentumBeforeCollision =
        momentumReadout massUnit lengthUnit timeUnit
          setup.horizontalMomentumAfterCollision

/-!
Kinetic-energy definition, gravitational potential-energy gain, and
mechanical-energy conservation for the frictionless ascent after the
inelastic collision. Energy conservation is deliberately not asserted across
the collision itself.
-/
structure SatisfiesFrictionlessAscentEnergyLaws
    (setup : IceValleyCollisionSetup) : Prop where
  translationalKineticEnergyLaw :
    ∀ (stage : AscentStage) (massUnit : MassUnit)
        (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      2 * energyReadout massUnit lengthUnit timeUnit
          (setup.translationalKineticEnergy stage) =
        massReadout massUnit setup.combinedMass *
          speedReadout lengthUnit timeUnit (setup.ascentSpeed stage) ^ 2
  gravitationalPotentialEnergyGain :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
            (setup.gravitationalPotentialEnergy .highestPoint) -
          energyReadout massUnit lengthUnit timeUnit
            (setup.gravitationalPotentialEnergy
              .valleyFloorImmediatelyAfterCollision) =
        massReadout massUnit setup.combinedMass *
          accelerationReadout lengthUnit timeUnit
            setup.gravitationalAccelerationMagnitude *
          lengthReadout lengthUnit setup.maximumRiseAboveValleyFloor
  mechanicalEnergyConservation :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      energyReadout massUnit lengthUnit timeUnit
            (setup.translationalKineticEnergy
              .valleyFloorImmediatelyAfterCollision) +
          energyReadout massUnit lengthUnit timeUnit
            (setup.gravitationalPotentialEnergy
              .valleyFloorImmediatelyAfterCollision) =
        energyReadout massUnit lengthUnit timeUnit
            (setup.translationalKineticEnergy .highestPoint) +
          energyReadout massUnit lengthUnit timeUnit
            (setup.gravitationalPotentialEnergy .highestPoint)

/-! ## Derived relations, displayed choices, and current target -/

/-- The four height choices printed with the problem. -/
inductive HeightAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre value printed beside each answer label. -/
def displayedHeightInMeters : HeightAnswerChoice → ℝ
  | .A => 8 / 5
  | .B => 6 / 5
  | .C => 19 / 10
  | .D => 3 / 2

/-- The answer label stored in the source dataset; metadata, not a premise. -/
def recordedDatasetAnswer : HeightAnswerChoice := .B

/-- A displayed choice is closest to an exact physical height. -/
def IsClosestHeightChoice
    (exactHeightInMeters : ℝ) (choice : HeightAnswerChoice) : Prop :=
  ∀ other : HeightAnswerChoice,
    |exactHeightInMeters - displayedHeightInMeters choice| ≤
      |exactHeightInMeters - displayedHeightInMeters other|

/-- A displayed choice is the unique closest choice. -/
def IsUniqueClosestHeightChoice
    (exactHeightInMeters : ℝ) (choice : HeightAnswerChoice) : Prop :=
  IsClosestHeightChoice exactHeightInMeters choice ∧
    ∀ other : HeightAnswerChoice,
      IsClosestHeightChoice exactHeightInMeters other → other = choice

/-!
Momentum conservation through the sticking collision fixes the compound
object's speed on the valley floor at `6 m/s`. This is a derived conclusion,
not a premise.
-/
lemma post_collision_speed_is_six_meters_per_second
    (setup : IceValleyCollisionSetup)
    (hScenario : MatchesIceValleyScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalIceValleyParameters setup)
    (hCollision : SatisfiesStickingCollisionMomentumLaws setup) :
    speedInMetersPerSecond
      (setup.ascentSpeed .valleyFloorImmediatelyAfterCollision) = 6 := by
  have hmMoving := hReadouts.movingChunkMassKilograms
  have hmStationary := hReadouts.stationaryChunkMassKilograms
  have hvMoving := hReadouts.movingChunkInitialSpeedMetersPerSecond
  simp only [massInKilograms] at hmMoving hmStationary
  simp only [speedInMetersPerSecond] at hvMoving ⊢
  have hRest :=
    hScenario.secondChunkInitiallyAtRest LengthUnit.meters TimeUnit.seconds
  have hCompound :=
    hCollision.compoundMassIsSum MassUnit.kilograms
  have hBefore :=
    hCollision.momentumBeforeFactorization
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hAfter :=
    hCollision.momentumAfterFactorization
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hConservation :=
    hCollision.horizontalMomentumConservation
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  nlinarith

/-!
Mechanical-energy conservation during the ascent gives the exact height
`v²/(2g) = 90/49 m` under standard terrestrial gravity.
-/
lemma maximum_rise_is_ninety_over_forty_nine_meters
    (setup : IceValleyCollisionSetup)
    (hScenario : MatchesIceValleyScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardTerrestrialGravity setup)
    (hPhysical : HasPhysicalIceValleyParameters setup)
    (hCollision : SatisfiesStickingCollisionMomentumLaws setup)
    (hEnergy : SatisfiesFrictionlessAscentEnergyLaws setup) :
    lengthInMeters setup.maximumRiseAboveValleyFloor = 90 / 49 := by
  have hv :=
    post_collision_speed_is_six_meters_per_second
      setup hScenario hReadouts hPhysical hCollision
  have hMass := hPhysical.combinedMassPositive
  have hg := hGravity.gravityMetersPerSecondSquared
  simp only [speedInMetersPerSecond] at hv
  simp only [massInKilograms] at hMass
  simp only [accelerationInMetersPerSecondSquared] at hg
  simp only [lengthInMeters]
  have hStop :=
    hScenario.compoundStopsAtHighestPoint LengthUnit.meters TimeUnit.seconds
  have hKFloor :=
    hEnergy.translationalKineticEnergyLaw
      AscentStage.valleyFloorImmediatelyAfterCollision
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hKHigh :=
    hEnergy.translationalKineticEnergyLaw
      AscentStage.highestPoint
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hPotential :=
    hEnergy.gravitationalPotentialEnergyGain
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  have hMechanical :=
    hEnergy.mechanicalEnergyConservation
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  norm_num [hv] at hKFloor
  norm_num [hStop] at hKHigh
  norm_num [hg] at hPotential
  have hProduct :
      massReadout MassUnit.kilograms setup.combinedMass *
          (lengthReadout LengthUnit.meters setup.maximumRiseAboveValleyFloor -
            90 / 49) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hProduct with hMassZero | hHeight
  · exact (ne_of_gt hMass hMassZero).elim
  · nlinarith

/-!
The combined chunks rise exactly `90/49 m`, and C (`1.9 m`) is the unique
closest displayed choice. The inconsistent recorded dataset label B is not
used as a premise or conclusion.

This formalizes `thm:physics:phyx_mini_0764:target`.
-/
theorem problem_phyx_mini_0764
    (setup : IceValleyCollisionSetup)
    (hScenario : MatchesIceValleyScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hGravity : UsesStandardTerrestrialGravity setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hPhysical : HasPhysicalIceValleyParameters setup)
    (hCollision : SatisfiesStickingCollisionMomentumLaws setup)
    (hEnergy : SatisfiesFrictionlessAscentEnergyLaws setup) :
    lengthInMeters setup.maximumRiseAboveValleyFloor = 90 / 49 ∧
      IsUniqueClosestHeightChoice
        (lengthInMeters setup.maximumRiseAboveValleyFloor) .C := by
  have hHeight :=
    maximum_rise_is_ninety_over_forty_nine_meters
      setup hScenario hReadouts hGravity hPhysical hCollision hEnergy
  refine ⟨hHeight, ?_⟩
  rw [hHeight]
  constructor
  · intro other
    cases other <;>
      norm_num [IsClosestHeightChoice, displayedHeightInMeters,
        abs_of_nonneg, abs_of_nonpos]
  · intro other hOther
    unfold IsClosestHeightChoice at hOther
    cases other with
    | A =>
        have h := hOther .C
        norm_num [displayedHeightInMeters, abs_of_nonneg, abs_of_nonpos] at h
    | B =>
        have h := hOther .C
        norm_num [displayedHeightInMeters, abs_of_nonneg, abs_of_nonpos] at h
    | C => rfl
    | D =>
        have h := hOther .C
        norm_num [displayedHeightInMeters, abs_of_nonneg, abs_of_nonpos] at h

end PhyXMiniProblems.ProblemPhyXMini0764
