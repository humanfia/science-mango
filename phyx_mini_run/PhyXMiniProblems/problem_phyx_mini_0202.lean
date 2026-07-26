import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0202

open Dimension

/-!
# Bullet embedded in a spring-mounted block

A bullet of mass `7.870 g` travels horizontally to the right and embeds in a
stationary `4.148 kg` wooden block on a smooth surface. The block is attached
to a spring of stiffness `162.7 N/m`; the embedded bullet-block composite then
compresses the spring by a maximum distance of `9.460 cm`.

The physical quantities below are unit-independent Physlib quantities. Real
numbers occur only as readouts in named units, in dimensionless numerical
data, and in the printed answer choices.
-/

/-- A nonnegative physical mass, independent of its readout unit. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, independent of its readout unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative speed, with dimension length per time. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Spring stiffness, with dimension mass per time squared (`N/m`). -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a speed in the coherent length-per-time unit selected below. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read spring stiffness in the coherent mass-per-time-squared unit. -/
def stiffnessReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout used for the two masses and the governing laws. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Gram readout used for the bullet mass stated in the problem. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Meter readout used for spring displacements. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimeter readout used for the measured maximum compression. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Speed readout in meters per SI second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Spring-stiffness readout in kilograms per second squared, i.e. newtons per meter. -/
def stiffnessInNewtonsPerMeter (stiffness : SpringStiffnessQuantity) : ℝ :=
  stiffnessReadout MassUnit.kilograms TimeUnit.seconds stiffness

/-- The two moments depicted by the upper and lower panels of the image. -/
inductive FigurePanel where
  | beforeImpact
  | maximumCompression
  deriving DecidableEq, Repr

/-- Objects distinguished in the supplied two-panel figure. -/
inductive FigureObject where
  | bullet
  | block
  | embeddedComposite
  | spring
  | rightWall
  | horizontalSurface
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the supplied figure. -/
inductive FigureLabel where
  | bulletMass_m
  | blockMass_M
  | combinedMass_M_plus_m
  | springConstant_k
  | bulletVelocity_v
  | compression_9_460_cm
  deriving DecidableEq, Repr

/-- Horizontal direction of the bullet's velocity arrow in the upper panel. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Qualitative collision outcome represented in the lower panel. -/
inductive CollisionOutcome where
  | bulletEmbeddedInBlock
  | bodiesSeparate
  deriving DecidableEq, Repr

/-- Surface idealization stated in the prose. -/
inductive SurfaceCondition where
  | smoothFrictionless
  | resistive
  deriving DecidableEq, Repr

/-!
Qualitative evidence transcribed from the primary image. The numerical
compression datum remains a readout of the physical displacement in the
setup; `showsLabel` only records that its label appears in the figure.
-/
structure BallisticSpringFigure where
  showsObject : FigurePanel → FigureObject → Bool
  showsLabel : FigurePanel → FigureLabel → Bool
  isLeftOf : FigurePanel → FigureObject → FigureObject → Bool
  bulletVelocityDirection : HorizontalDirection
  springConnectsBodyToRightWall : FigurePanel → Bool
  bulletEmbeddedAtMaximumCompression : Bool
  compressionArrowBetweenBlockPositions : Bool

/-!
All independent quantities used in the experiment. In particular,
`initialBulletSpeed` is an unconstrained physical speed until the data and
governing laws are supplied; no field assigns it an answer-choice value.
-/
structure BallisticSpringSetup where
  bulletMass : MassQuantity
  blockMass : MassQuantity
  springStiffness : SpringStiffnessQuantity
  initialBulletSpeed : SpeedQuantity
  initialBlockSpeed : SpeedQuantity
  postImpactCompositeSpeed : SpeedQuantity
  speedAtMaximumCompression : SpeedQuantity
  initialSpringCompression : LengthQuantity
  maximumSpringCompression : LengthQuantity
  surfaceCondition : SurfaceCondition
  collisionOutcome : CollisionOutcome
  figure : BallisticSpringFigure

/-!
Numerical readouts stated in the problem, together with the initial and final
boundary conditions implicit in "resting" and "maximum compression". The
requested muzzle speed does not occur here.
-/
structure MatchesProblemReadouts (setup : BallisticSpringSetup) : Prop where
  bulletMassGrams : massInGrams setup.bulletMass = 787 / 100
  blockMassKilograms : massInKilograms setup.blockMass = 1037 / 250
  springStiffnessNewtonsPerMeter :
    stiffnessInNewtonsPerMeter setup.springStiffness = 1627 / 10
  maximumCompressionCentimeters :
    lengthInCentimeters setup.maximumSpringCompression = 473 / 50
  blockInitiallyAtRest :
    speedInMetersPerSecond setup.initialBlockSpeed = 0
  springInitiallyUncompressed :
    lengthInMeters setup.initialSpringCompression = 0
  compositeAtRestAtMaximumCompression :
    speedInMetersPerSecond setup.speedAtMaximumCompression = 0

/-!
Qualitative scenario and primary-image facts. The upper panel places the
right-moving bullet to the left of the block and the block to the left of the
wall-mounted spring. The lower panel shows the embedded composite and the
compression annotation.
-/
def MatchesScenarioAndSuppliedFigure (setup : BallisticSpringSetup) : Prop :=
  setup.surfaceCondition = .smoothFrictionless ∧
    setup.collisionOutcome = .bulletEmbeddedInBlock ∧
    setup.figure.bulletVelocityDirection = .right ∧
    setup.figure.springConnectsBodyToRightWall .beforeImpact = true ∧
    setup.figure.springConnectsBodyToRightWall .maximumCompression = true ∧
    setup.figure.bulletEmbeddedAtMaximumCompression = true ∧
    setup.figure.compressionArrowBetweenBlockPositions = true ∧
    setup.figure.showsObject .beforeImpact .bullet = true ∧
    setup.figure.showsObject .beforeImpact .block = true ∧
    setup.figure.showsObject .beforeImpact .spring = true ∧
    setup.figure.showsObject .beforeImpact .rightWall = true ∧
    setup.figure.showsObject .beforeImpact .horizontalSurface = true ∧
    setup.figure.showsObject .maximumCompression .embeddedComposite = true ∧
    setup.figure.showsObject .maximumCompression .spring = true ∧
    setup.figure.showsObject .maximumCompression .rightWall = true ∧
    setup.figure.showsObject .maximumCompression .horizontalSurface = true ∧
    setup.figure.isLeftOf .beforeImpact .bullet .block = true ∧
    setup.figure.isLeftOf .beforeImpact .block .rightWall = true ∧
    setup.figure.isLeftOf .maximumCompression .embeddedComposite .rightWall = true ∧
    setup.figure.showsLabel .beforeImpact .bulletMass_m = true ∧
    setup.figure.showsLabel .beforeImpact .blockMass_M = true ∧
    setup.figure.showsLabel .beforeImpact .springConstant_k = true ∧
    setup.figure.showsLabel .beforeImpact .bulletVelocity_v = true ∧
    setup.figure.showsLabel .maximumCompression .combinedMass_M_plus_m = true ∧
    setup.figure.showsLabel .maximumCompression .compression_9_460_cm = true

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
def HasPhysicalBallisticSpringParameters
    (setup : BallisticSpringSetup) : Prop :=
  0 < massInKilograms setup.bulletMass ∧
    0 < massInKilograms setup.blockMass ∧
    0 < stiffnessInNewtonsPerMeter setup.springStiffness ∧
    0 < lengthInMeters setup.maximumSpringCompression ∧
    0 < speedInMetersPerSecond setup.initialBulletSpeed ∧
    0 < speedInMetersPerSecond setup.postImpactCompositeSpeed

/-!
One-dimensional momentum conservation during the short perfectly inelastic
collision. It is stated in every coherent selection of mass, length, and
time units and retains the initially stationary block term explicitly.
-/
structure SatisfiesCollisionMomentumConservation
    (setup : BallisticSpringSetup) : Prop where
  momentumBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit setup.bulletMass *
          speedReadout lengthUnit timeUnit setup.initialBulletSpeed +
        massReadout massUnit setup.blockMass *
          speedReadout lengthUnit timeUnit setup.initialBlockSpeed =
      (massReadout massUnit setup.bulletMass +
          massReadout massUnit setup.blockMass) *
        speedReadout lengthUnit timeUnit setup.postImpactCompositeSpeed

/-!
Mechanical-energy conservation from immediately after impact until maximum
compression. Multiplying the usual kinetic-plus-spring-potential equation by
two gives the displayed relation. Collision energy is deliberately not
conserved: this law applies only after the embedded composite has formed.
-/
structure SatisfiesEnergyConservationDuringCompression
    (setup : BallisticSpringSetup) : Prop where
  energyBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      (massReadout massUnit setup.bulletMass +
          massReadout massUnit setup.blockMass) *
            speedReadout lengthUnit timeUnit
              setup.postImpactCompositeSpeed ^ 2 +
        stiffnessReadout massUnit timeUnit setup.springStiffness *
            lengthReadout lengthUnit setup.initialSpringCompression ^ 2 =
      (massReadout massUnit setup.bulletMass +
          massReadout massUnit setup.blockMass) *
            speedReadout lengthUnit timeUnit
              setup.speedAtMaximumCompression ^ 2 +
        stiffnessReadout massUnit timeUnit setup.springStiffness *
            lengthReadout lengthUnit setup.maximumSpringCompression ^ 2

/-!
Eliminating the intermediate composite speed yields the exact squared-speed
relation. This is a derived conclusion, not a premise of the main theorem.
-/
lemma initialBulletSpeed_squared_relation
    (setup : BallisticSpringSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalBallisticSpringParameters setup)
    (hMomentum : SatisfiesCollisionMomentumConservation setup)
    (hEnergy : SatisfiesEnergyConservationDuringCompression setup) :
    massInKilograms setup.bulletMass ^ 2 *
        speedInMetersPerSecond setup.initialBulletSpeed ^ 2 =
      (massInKilograms setup.bulletMass + massInKilograms setup.blockMass) *
        stiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters setup.maximumSpringCompression ^ 2 := by
  have hMomentumSI :=
    hMomentum.momentumBalance
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    massInKilograms setup.bulletMass *
          speedInMetersPerSecond setup.initialBulletSpeed +
        massInKilograms setup.blockMass *
          speedInMetersPerSecond setup.initialBlockSpeed =
      (massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) *
        speedInMetersPerSecond setup.postImpactCompositeSpeed
    at hMomentumSI
  rw [hReadouts.blockInitiallyAtRest] at hMomentumSI
  norm_num at hMomentumSI
  have hEnergySI :=
    hEnergy.energyBalance
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    (massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) *
            speedInMetersPerSecond setup.postImpactCompositeSpeed ^ 2 +
        stiffnessInNewtonsPerMeter setup.springStiffness *
            lengthInMeters setup.initialSpringCompression ^ 2 =
      (massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) *
            speedInMetersPerSecond setup.speedAtMaximumCompression ^ 2 +
        stiffnessInNewtonsPerMeter setup.springStiffness *
            lengthInMeters setup.maximumSpringCompression ^ 2
    at hEnergySI
  rw [hReadouts.springInitiallyUncompressed,
    hReadouts.compositeAtRestAtMaximumCompression] at hEnergySI
  norm_num at hEnergySI
  calc
    massInKilograms setup.bulletMass ^ 2 *
          speedInMetersPerSecond setup.initialBulletSpeed ^ 2 =
        (massInKilograms setup.bulletMass *
          speedInMetersPerSecond setup.initialBulletSpeed) ^ 2 := by ring
    _ = ((massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) *
        speedInMetersPerSecond setup.postImpactCompositeSpeed) ^ 2 := by
      rw [hMomentumSI]
    _ = (massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) *
        ((massInKilograms setup.bulletMass +
            massInKilograms setup.blockMass) *
          speedInMetersPerSecond setup.postImpactCompositeSpeed ^ 2) := by
      ring
    _ = (massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) *
        (stiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters setup.maximumSpringCompression ^ 2) := by
      rw [hEnergySI]
    _ = (massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) *
        stiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters setup.maximumSpringCompression ^ 2 := by ring

/-!
The positive solution of the squared relation, with all source measurements
converted to SI units. The decimal answer is obtained only after rounding
this exact radical expression.
-/
lemma initialBulletSpeed_exact_readout
    (setup : BallisticSpringSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hPhysical : HasPhysicalBallisticSpringParameters setup)
    (hMomentum : SatisfiesCollisionMomentumConservation setup)
    (hEnergy : SatisfiesEnergyConservationDuringCompression setup) :
    speedInMetersPerSecond setup.initialBulletSpeed =
      (473 / 5000) *
        Real.sqrt ((1627 / 10) * (1037 / 250 + 787 / 100000)) /
          (787 / 100000) := by
  have massGrams_eq (mass : MassQuantity) :
      massInGrams mass = 1000 * massInKilograms mass := by
    change
      ((mass {UnitChoices.SI with mass := MassUnit.grams}).val : ℝ) =
        1000 * ((mass UnitChoices.SI).val : ℝ)
    rw [mass.2 UnitChoices.SI
      {UnitChoices.SI with mass := MassUnit.grams}]
    have hScale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with mass := MassUnit.grams}
          (dim (WithDim M𝓭 NNReal)) = 1000 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, MassUnit.grams,
        MassUnit.kilograms, MassUnit.scale, MassUnit.div_eq_val, M𝓭]
      rfl
    rw [hScale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have lengthCentimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    change
      ((length
        {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ) =
        100 * ((length UnitChoices.SI).val : ℝ)
    rw [length.2 UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.centimeters}]
    have hScale :
        UnitChoices.dimScale UnitChoices.SI
          {UnitChoices.SI with length := LengthUnit.centimeters}
          (dim (WithDim L𝓭 NNReal)) = 100 := by
      apply NNReal.eq
      norm_num [UnitChoices.dimScale, LengthUnit.centimeters,
        LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
      rfl
    rw [hScale]
    norm_num [WithDim.smul_val, NNReal.smul_def, smul_eq_mul]
  have hBulletMassGrams := hReadouts.bulletMassGrams
  have hBulletMass :
      massInKilograms setup.bulletMass = 787 / 100000 := by
    rw [massGrams_eq] at hBulletMassGrams
    norm_num at hBulletMassGrams ⊢
    linarith only [hBulletMassGrams]
  have hCompressionCentimeters := hReadouts.maximumCompressionCentimeters
  have hCompression :
      lengthInMeters setup.maximumSpringCompression = 473 / 5000 := by
    rw [lengthCentimeters_eq] at hCompressionCentimeters
    norm_num at hCompressionCentimeters ⊢
    linarith only [hCompressionCentimeters]
  have hSquared := initialBulletSpeed_squared_relation
    setup hReadouts hPhysical hMomentum hEnergy
  rw [hBulletMass, hReadouts.blockMassKilograms,
    hReadouts.springStiffnessNewtonsPerMeter, hCompression] at hSquared
  have hSpeedPositive :
      0 < speedInMetersPerSecond setup.initialBulletSpeed :=
    hPhysical.2.2.2.2.1
  have hSqrtSquared :
      Real.sqrt ((1627 / 10) * (1037 / 250 + 787 / 100000)) ^ 2 =
        (1627 / 10) * (1037 / 250 + 787 / 100000) :=
    Real.sq_sqrt (by norm_num)
  have hExactExpressionPositive :
      0 <
        (473 / 5000) *
          Real.sqrt ((1627 / 10) * (1037 / 250 + 787 / 100000)) /
            (787 / 100000) := by
    positivity
  have hSquares :
      speedInMetersPerSecond setup.initialBulletSpeed ^ 2 =
        ((473 / 5000) *
          Real.sqrt ((1627 / 10) * (1037 / 250 + 787 / 100000)) /
            (787 / 100000)) ^ 2 := by
    norm_num at hSquared hSqrtSquared ⊢
    nlinarith only [hSquared, hSqrtSquared]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hSquares) with hExact | hNegated
  · exact hExact
  · nlinarith only [hSpeedPositive, hExactExpressionPositive, hNegated]

/-- Labels attached to the four speeds printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed answer speeds, read in meters per second. -/
def displayedAnswerSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 3026 / 10
  | .B => 3326 / 10
  | .C => 3226 / 10
  | .D => 3126 / 10

/-- The dataset's recorded answer label; this metadata is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- Agreement with a displayed speed after rounding to the nearest `0.1 m/s`. -/
def RoundsToNearestTenthMeterPerSecond
    (speed : SpeedQuantity) (displayedSpeed : ℝ) : Prop :=
  |speedInMetersPerSecond speed - displayedSpeed| < (1 / 20 : ℝ)

/-- The physical muzzle speed rounds to the number printed beside a choice. -/
def MatchesAnswerChoice
    (setup : BallisticSpringSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestTenthMeterPerSecond setup.initialBulletSpeed
    (displayedAnswerSpeedInMetersPerSecond choice)

/-!
Momentum conservation in the embedding collision and energy conservation in
the later frictionless compression predict approximately `312.6 m/s`, i.e.
answer choice D.

This is the formal target corresponding to
`thm:physics:phyx_mini_0202:target`.
-/
theorem problem_phyx_mini_0202
    (setup : BallisticSpringSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hScenario : MatchesScenarioAndSuppliedFigure setup)
    (hPhysical : HasPhysicalBallisticSpringParameters setup)
    (hMomentum : SatisfiesCollisionMomentumConservation setup)
    (hEnergy : SatisfiesEnergyConservationDuringCompression setup) :
    RoundsToNearestTenthMeterPerSecond setup.initialBulletSpeed (3126 / 10) ∧
      MatchesAnswerChoice setup .D := by
  have hExact := initialBulletSpeed_exact_readout
    setup hReadouts hPhysical hMomentum hEnergy
  have hSqrtLower :
      (26003 / 1000 : ℝ) <
        Real.sqrt ((1627 / 10) * (1037 / 250 + 787 / 100000)) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hSqrtUpper :
      Real.sqrt ((1627 / 10) * (1037 / 250 + 787 / 100000)) <
        (6501 / 250 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hRounded :
      RoundsToNearestTenthMeterPerSecond
        setup.initialBulletSpeed (3126 / 10) := by
    rw [RoundsToNearestTenthMeterPerSecond, hExact, abs_lt]
    constructor
    · nlinarith only [hSqrtLower]
    · nlinarith only [hSqrtUpper]
  refine ⟨hRounded, ?_⟩
  simpa [MatchesAnswerChoice, displayedAnswerSpeedInMetersPerSecond]
    using hRounded

end PhyXMiniProblems.ProblemPhyXMini0202
