import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0763

open Dimension

/-!
# Stone rebounding from a spring-mounted block

A `3.00 kg` stone moving right at `8.00 m/s` strikes a stationary `15.0 kg`
block attached to a very light spring of stiffness `500.0 N/m`.  The stone
rebounds left at `2.00 m/s`.  The table is horizontal and frictionless, and the
question asks for the block's maximum spring compression after the collision.

Mass, signed one-dimensional velocity, length, spring stiffness, and energy
are represented by unit-independent Physlib quantities.  Real numbers occur
only at coherent unit-readout boundaries and in the displayed answer data.

Assumption/target split:

* `MatchesProblemReadouts` contains only numerical data stated in the prose
  and the boundary conditions implicit in "resting" and "maximum";
* `MatchesScenarioAndPrimaryFigure` records qualitative idealizations and the
  labels and geometry visible in image `763.png`;
* `SatisfiesImpulsiveCollisionLaws` states momentum conservation and position
  continuity during the short impact;
* the kinetic-energy, Hooke-spring-energy, and post-impact conservation
  structures state the governing laws during later compression; and
* the exact maximum compression and choice B occur only in conclusions.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length or compression magnitude. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed horizontal velocity, with dimension `L T⁻¹`. -/
abbrev HorizontalVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A nonnegative linear-spring stiffness, with dimension `M T⁻²` (`N/m`). -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed velocity in coherent selected length and time units. -/
def horizontalVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : HorizontalVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read spring stiffness in coherent selected mass and time units. -/
def springStiffnessReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout of a spring compression. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Metres-per-second readout, positive to the right and negative to the left. -/
def horizontalVelocityInMetersPerSecond
    (velocity : HorizontalVelocityQuantity) : ℝ :=
  horizontalVelocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Newton-per-metre readout of a physical spring stiffness. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  springStiffnessReadout MassUnit.kilograms TimeUnit.seconds stiffness

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Process states and primary-figure vocabulary -/

/-- Bodies participating in the collision. -/
inductive Body where
  | stone
  | block
  deriving DecidableEq, Fintype, Repr

/-- The three instants needed by the collision-and-compression calculation. -/
inductive ProcessInstant where
  | beforeImpact
  | immediatelyAfterImpact
  | maximumCompression
  deriving DecidableEq, Fintype, Repr

/-- Horizontal directions used by the prose and velocity arrow. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Surface idealizations relevant to the block's motion. -/
inductive SurfaceCondition where
  | horizontalFrictionless
  | resistive
  deriving DecidableEq, Repr

/-- Mass idealization stated for the spring. -/
inductive SpringMassIdealization where
  | veryLightNegligibleMass
  | massive
  deriving DecidableEq, Repr

/-- Qualitative outcome of the stone--block impact. -/
inductive CollisionOutcome where
  | stoneReboundsAndSeparates
  | stoneEmbeds
  deriving DecidableEq, Repr

/-- Impact-scale approximation used for the collision momentum balance. -/
inductive CollisionImpulseModel where
  | negligibleExternalHorizontalImpulse
  | includesExternalHorizontalImpulse
  deriving DecidableEq, Repr

/-- Objects and lines visible in the supplied raster. -/
inductive FigureObject where
  | stone
  | block
  | coilSpring
  | rightWall
  | horizontalTableLine
  deriving DecidableEq, Fintype, Repr

/-- Numerical labels printed in image `763.png`. -/
inductive FigureLabel where
  | stoneMass_3_00_kg
  | stoneSpeed_8_00_mps
  | blockMass_15_0_kg
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative transcription of the primary image.  The raster fixes the
left-to-right topology and the initial green velocity arrow but contains no
compression scale or post-impact drawing.
-/
structure StoneBlockSpringFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  isLeftOf : FigureObject → FigureObject → Bool
  stoneVelocityArrowDirection : HorizontalDirection
  stoneVelocityArrowIsGreen : Bool
  springTouchesBlock : Bool
  springMeetsRightWall : Bool
  containsCompressionScale : Bool
  containsPostImpactPanel : Bool

/-!
Independent physical quantities for the collision and later compression.
In particular, `springCompressionAt .maximumCompression` is an unconstrained
physical length; it is not defined from the recorded answer or a radical.
-/
structure StoneBlockSpringSetup where
  bodyMass : Body → MassQuantity
  horizontalVelocityAt : ProcessInstant → Body → HorizontalVelocityQuantity
  springStiffness : SpringStiffnessQuantity
  springCompressionAt : ProcessInstant → LengthQuantity
  blockKineticEnergyAt : ProcessInstant → DimEnergy
  springPotentialEnergyAt : ProcessInstant → DimEnergy
  surfaceCondition : SurfaceCondition
  springMassIdealization : SpringMassIdealization
  collisionOutcome : CollisionOutcome
  collisionImpulseModel : CollisionImpulseModel
  springAttachedToBlock : Bool
  maximumCompressionIsTurningPoint : Bool
  figure : StoneBlockSpringFigure

/-! ## Source data, scenario facts, and governing laws -/

/-!
The numerical readouts stated in the problem.  The zero block velocity at the
turning point expresses the meaning of maximum compression, not its distance.
The block's post-impact speed and maximum compression are absent.
-/
structure MatchesProblemReadouts (setup : StoneBlockSpringSetup) : Prop where
  stoneMassKilograms :
    massInKilograms (setup.bodyMass .stone) = 3
  blockMassKilograms :
    massInKilograms (setup.bodyMass .block) = 15
  springStiffnessNewtonsPerMeter :
    springStiffnessInNewtonsPerMeter setup.springStiffness = 500
  stoneInitiallyMovesRightAtEight :
    horizontalVelocityInMetersPerSecond
      (setup.horizontalVelocityAt .beforeImpact .stone) = 8
  blockInitiallyAtRest :
    horizontalVelocityInMetersPerSecond
      (setup.horizontalVelocityAt .beforeImpact .block) = 0
  stoneReboundsLeftAtTwo :
    horizontalVelocityInMetersPerSecond
      (setup.horizontalVelocityAt .immediatelyAfterImpact .stone) = -2
  springInitiallyUncompressed :
    lengthInMeters (setup.springCompressionAt .beforeImpact) = 0
  blockAtRestAtMaximumCompression :
    horizontalVelocityInMetersPerSecond
      (setup.horizontalVelocityAt .maximumCompression .block) = 0

/-! Qualitative prose assumptions and facts read directly from image `763.png`. -/
structure MatchesScenarioAndPrimaryFigure
    (setup : StoneBlockSpringSetup) : Prop where
  frictionlessHorizontalTable :
    setup.surfaceCondition = .horizontalFrictionless
  veryLightSpring :
    setup.springMassIdealization = .veryLightNegligibleMass
  stoneRebounds :
    setup.collisionOutcome = .stoneReboundsAndSeparates
  shortImpactHasNegligibleExternalImpulse :
    setup.collisionImpulseModel = .negligibleExternalHorizontalImpulse
  springIsAttachedToBlock : setup.springAttachedToBlock = true
  turningPointIsMaximumCompression :
    setup.maximumCompressionIsTurningPoint = true
  everyDepictedObjectIsShown :
    ∀ object, setup.figure.objectShown object = true
  everyPrintedLabelIsShown :
    ∀ label, setup.figure.labelShown label = true
  stoneIsLeftOfBlock :
    setup.figure.isLeftOf .stone .block = true
  blockIsLeftOfSpring :
    setup.figure.isLeftOf .block .coilSpring = true
  springIsLeftOfWall :
    setup.figure.isLeftOf .coilSpring .rightWall = true
  initialArrowPointsRight :
    setup.figure.stoneVelocityArrowDirection = .right
  initialArrowIsGreen : setup.figure.stoneVelocityArrowIsGreen = true
  springTouchesBlock : setup.figure.springTouchesBlock = true
  springMeetsWall : setup.figure.springMeetsRightWall = true
  noCompressionScale : setup.figure.containsCompressionScale = false
  noPostImpactPanel : setup.figure.containsPostImpactPanel = false

/-- Positivity conditions selecting the physically meaningful compression branch. -/
structure HasPhysicalParameters (setup : StoneBlockSpringSetup) : Prop where
  stoneMassPositive : 0 < massInKilograms (setup.bodyMass .stone)
  blockMassPositive : 0 < massInKilograms (setup.bodyMass .block)
  springStiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness
  maximumCompressionPositive :
    0 < lengthInMeters (setup.springCompressionAt .maximumCompression)

/-!
One-dimensional momentum conservation during the short impact, together with
continuity of the block/spring position across an impulsive collision.  The
balance is stated in every coherent selection of mass, length, and time units.
It does not prescribe the block's post-impact velocity.
-/
structure SatisfiesImpulsiveCollisionLaws
    (setup : StoneBlockSpringSetup) : Prop where
  momentumBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit (setup.bodyMass .stone) *
            horizontalVelocityReadout lengthUnit timeUnit
              (setup.horizontalVelocityAt .beforeImpact .stone) +
          massReadout massUnit (setup.bodyMass .block) *
            horizontalVelocityReadout lengthUnit timeUnit
              (setup.horizontalVelocityAt .beforeImpact .block) =
        massReadout massUnit (setup.bodyMass .stone) *
            horizontalVelocityReadout lengthUnit timeUnit
              (setup.horizontalVelocityAt .immediatelyAfterImpact .stone) +
          massReadout massUnit (setup.bodyMass .block) *
            horizontalVelocityReadout lengthUnit timeUnit
              (setup.horizontalVelocityAt .immediatelyAfterImpact .block)
  compressionContinuousAcrossImpact :
    ∀ lengthUnit : LengthUnit,
      lengthReadout lengthUnit
          (setup.springCompressionAt .immediatelyAfterImpact) =
        lengthReadout lengthUnit
          (setup.springCompressionAt .beforeImpact)

/-- Translational kinetic energy of the block is `K = (1/2) M v²`. -/
structure SatisfiesBlockKineticEnergyLaw
    (setup : StoneBlockSpringSetup) : Prop where
  energyFormula : ∀ instant,
    energyInJoules (setup.blockKineticEnergyAt instant) =
      (1 / 2 : ℝ) * massInKilograms (setup.bodyMass .block) *
        horizontalVelocityInMetersPerSecond
          (setup.horizontalVelocityAt instant .block) ^ 2

/-- Potential energy of the light linear spring is `U = (1/2) k x²`. -/
structure SatisfiesHookeSpringPotentialEnergyLaw
    (setup : StoneBlockSpringSetup) : Prop where
  energyFormula : ∀ instant,
    energyInJoules (setup.springPotentialEnergyAt instant) =
      (1 / 2 : ℝ) *
        springStiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters (setup.springCompressionAt instant) ^ 2

/-- Total block-plus-spring mechanical energy at a selected instant. -/
def blockSpringMechanicalEnergyInJoules
    (setup : StoneBlockSpringSetup) (instant : ProcessInstant) : ℝ :=
  energyInJoules (setup.blockKineticEnergyAt instant) +
    energyInJoules (setup.springPotentialEnergyAt instant)

/-!
On the frictionless table, block-plus-spring mechanical energy is conserved
from immediately after impact until the maximum-compression turning point.
No energy conservation across the stone--block collision is assumed.
-/
structure SatisfiesPostImpactMechanicalEnergyConservation
    (setup : StoneBlockSpringSetup) : Prop where
  energyBalance :
    blockSpringMechanicalEnergyInJoules setup .immediatelyAfterImpact =
      blockSpringMechanicalEnergyInJoules setup .maximumCompression

/-! ## Derived relations and displayed answer -/

/-- Momentum transfer from the rebounding stone gives the block speed `2 m/s`. -/
lemma blockVelocityImmediatelyAfterImpact_eq_two
    (setup : StoneBlockSpringSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hCollision : SatisfiesImpulsiveCollisionLaws setup) :
    horizontalVelocityInMetersPerSecond
      (setup.horizontalVelocityAt .immediatelyAfterImpact .block) = 2 := by
  have hMomentum := hCollision.momentumBalance
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    massInKilograms (setup.bodyMass .stone) *
          horizontalVelocityInMetersPerSecond
            (setup.horizontalVelocityAt .beforeImpact .stone) +
        massInKilograms (setup.bodyMass .block) *
          horizontalVelocityInMetersPerSecond
            (setup.horizontalVelocityAt .beforeImpact .block) =
      massInKilograms (setup.bodyMass .stone) *
          horizontalVelocityInMetersPerSecond
            (setup.horizontalVelocityAt .immediatelyAfterImpact .stone) +
        massInKilograms (setup.bodyMass .block) *
          horizontalVelocityInMetersPerSecond
            (setup.horizontalVelocityAt .immediatelyAfterImpact .block)
    at hMomentum
  rw [hReadouts.stoneMassKilograms, hReadouts.blockMassKilograms,
    hReadouts.stoneInitiallyMovesRightAtEight, hReadouts.blockInitiallyAtRest,
    hReadouts.stoneReboundsLeftAtTwo] at hMomentum
  linarith

/-!
The momentum and post-impact energy laws give the exact positive compression
`sqrt (3/25) m`.  This is a derived result, not a premise or definition.
-/
lemma maximumCompression_exact
    (setup : StoneBlockSpringSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hCollision : SatisfiesImpulsiveCollisionLaws setup)
    (hKinetic : SatisfiesBlockKineticEnergyLaw setup)
    (hSpring : SatisfiesHookeSpringPotentialEnergyLaw setup)
    (hEnergy : SatisfiesPostImpactMechanicalEnergyConservation setup) :
    lengthInMeters (setup.springCompressionAt .maximumCompression) =
      Real.sqrt (3 / 25 : ℝ) := by
  have hBlockVelocity :=
    blockVelocityImmediatelyAfterImpact_eq_two setup hReadouts hCollision
  have hCompressionAfterImpact :=
    hCollision.compressionContinuousAcrossImpact LengthUnit.meters
  change
    lengthInMeters (setup.springCompressionAt .immediatelyAfterImpact) =
      lengthInMeters (setup.springCompressionAt .beforeImpact)
    at hCompressionAfterImpact
  rw [hReadouts.springInitiallyUncompressed] at hCompressionAfterImpact
  have hKineticAfter :=
    hKinetic.energyFormula ProcessInstant.immediatelyAfterImpact
  have hKineticMaximum :=
    hKinetic.energyFormula ProcessInstant.maximumCompression
  have hSpringAfter :=
    hSpring.energyFormula ProcessInstant.immediatelyAfterImpact
  have hSpringMaximum :=
    hSpring.energyFormula ProcessInstant.maximumCompression
  have hBalance := hEnergy.energyBalance
  unfold blockSpringMechanicalEnergyInJoules at hBalance
  rw [hKineticAfter, hSpringAfter, hKineticMaximum, hSpringMaximum,
    hReadouts.blockMassKilograms, hReadouts.springStiffnessNewtonsPerMeter,
    hBlockVelocity, hCompressionAfterImpact,
    hReadouts.blockAtRestAtMaximumCompression] at hBalance
  have hCompressionSquared :
      lengthInMeters (setup.springCompressionAt .maximumCompression) ^ 2 =
        (3 / 25 : ℝ) := by
    norm_num at hBalance ⊢
    linarith
  have hRadicandNonnegative : (0 : ℝ) ≤ 3 / 25 := by norm_num
  have hSqrtSquared :
      Real.sqrt (3 / 25 : ℝ) ^ 2 = 3 / 25 :=
    Real.sq_sqrt hRadicandNonnegative
  have hSqrtNonnegative : 0 ≤ Real.sqrt (3 / 25 : ℝ) :=
    Real.sqrt_nonneg _
  nlinarith [hPhysical.maximumCompressionPositive]

/-- Labels attached to the four displayed distances. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Distance in metres printed beside each answer label. -/
def AnswerChoice.distanceInMeters : AnswerChoice → ℝ
  | .A => 231 / 1000
  | .B => 346 / 1000
  | .C => 549 / 1000
  | .D => 651 / 1000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement with a distance displayed to the nearest millimetre. -/
def AgreesWithThreeDecimalMeterReadout
    (length : LengthQuantity) (displayedMeters : ℝ) : Prop :=
  |lengthInMeters length - displayedMeters| < (1 / 2000 : ℝ)

/-- A choice reports the maximum compression to the displayed precision. -/
def AnswerChoiceReportsMaximumCompression
    (setup : StoneBlockSpringSetup) (choice : AnswerChoice) : Prop :=
  AgreesWithThreeDecimalMeterReadout
    (setup.springCompressionAt .maximumCompression)
    choice.distanceInMeters

/-!
The collision gives the block speed `2 m/s`; the later conversion of its
kinetic energy into spring energy gives `sqrt (3/25) m ≈ 0.346 m`, answer B.

This formalizes blueprint label `thm:physics:phyx_mini_0763:target`.
-/
theorem problem_phyx_mini_0763
    (setup : StoneBlockSpringSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hScenario : MatchesScenarioAndPrimaryFigure setup)
    (hPhysical : HasPhysicalParameters setup)
    (hCollision : SatisfiesImpulsiveCollisionLaws setup)
    (hKinetic : SatisfiesBlockKineticEnergyLaw setup)
    (hSpring : SatisfiesHookeSpringPotentialEnergyLaw setup)
    (hEnergy : SatisfiesPostImpactMechanicalEnergyConservation setup) :
    lengthInMeters (setup.springCompressionAt .maximumCompression) =
        Real.sqrt (3 / 25 : ℝ) ∧
      AnswerChoiceReportsMaximumCompression setup recordedDatasetAnswer := by
  have hExact := maximumCompression_exact setup hReadouts hPhysical hCollision
    hKinetic hSpring hEnergy
  constructor
  · exact hExact
  · unfold AnswerChoiceReportsMaximumCompression
      AgreesWithThreeDecimalMeterReadout recordedDatasetAnswer
      AnswerChoice.distanceInMeters
    rw [hExact, abs_lt]
    have hRadicandNonnegative : (0 : ℝ) ≤ 3 / 25 := by norm_num
    have hSqrtSquared :
        Real.sqrt (3 / 25 : ℝ) ^ 2 = 3 / 25 :=
      Real.sq_sqrt hRadicandNonnegative
    have hSqrtNonnegative : 0 ≤ Real.sqrt (3 / 25 : ℝ) :=
      Real.sqrt_nonneg _
    constructor
    · have hLowerSquared : (691 / 2000 : ℝ) ^ 2 < 3 / 25 := by
        norm_num
      nlinarith
    · have hUpperSquared : (3 / 25 : ℝ) < (693 / 2000 : ℝ) ^ 2 := by
        norm_num
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0763
