import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0260

open Dimension

/-!
# Bullet embedded in a spring-mounted block

A `9.5 g` bullet moving horizontally at `630 m/s` embeds in a stationary
`5.4 kg` block on a frictionless table.  The block is attached on its right to
a rigid support by a spring of stiffness `6000 N/m`.  Spring compression is
negligible during the collision; after the collision the embedded composite
executes simple harmonic motion.

Masses, lengths, speeds, and spring stiffnesses are unit-independent Physlib
quantities.  Real numbers occur only as scalar readouts in named units and in
the displayed numerical answer choices.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative speed magnitude, with dimension length per time. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Spring stiffness, with dimension mass per time squared (`N/m` in SI). -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

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

/-- Read a spring stiffness in a coherent mass-per-time-squared unit. -/
def stiffnessReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout used in the governing laws. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Gram readout used for the bullet datum. -/
def massInGrams (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.grams mass

/-- Metre readout used for spring displacements and amplitudes. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Speed readout in metres per SI second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds speed

/-- Spring-stiffness readout in newtons per metre. -/
def stiffnessInNewtonsPerMeter (stiffness : SpringStiffnessQuantity) : ℝ :=
  stiffnessReadout MassUnit.kilograms TimeUnit.seconds stiffness

/-! ## Labels and qualitative facts from the supplied figure -/

/-- Physical objects distinguished in the one-panel figure. -/
inductive FigureObject where
  | bullet
  | block
  | spring
  | rigidSupport
  | horizontalTable
  deriving DecidableEq, Repr

/-- Mathematical labels printed in the supplied figure. -/
inductive FigureLabel where
  | bulletMass_m
  | blockMass_M
  | springConstant_k
  | bulletVelocity_v
  deriving DecidableEq, Repr

/-- Horizontal direction of the velocity arrow. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Idealization of the horizontal surface stated in the prose. -/
inductive SurfaceCondition where
  | frictionless
  | resistive
  deriving DecidableEq, Repr

/-- Qualitative outcome of the bullet--block collision. -/
inductive CollisionOutcome where
  | bulletEmbeddedInBlock
  | bodiesSeparate
  deriving DecidableEq, Repr

/-- Raw qualitative evidence represented in the supplied image. -/
structure BallisticSpringFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  isLeftOf : FigureObject → FigureObject → Bool
  bulletVelocityDirection : HorizontalDirection
  springConnectsBlockToRigidSupport : Bool
  objectsAreHorizontallyAligned : Bool

/-!
Primary-image facts: the right-moving bullet lies to the left of the block,
and the block is joined on its right to the wall-mounted spring.  The
frictionless idealization and embedding outcome are stated in the prose and
are included alongside the image readout.
-/
def MatchesScenarioAndSuppliedFigure
    (surface : SurfaceCondition)
    (outcome : CollisionOutcome)
    (figure : BallisticSpringFigure) : Prop :=
  surface = .frictionless ∧
    outcome = .bulletEmbeddedInBlock ∧
    figure.bulletVelocityDirection = .right ∧
    figure.springConnectsBlockToRigidSupport = true ∧
    figure.objectsAreHorizontallyAligned = true ∧
    figure.showsObject .bullet = true ∧
    figure.showsObject .block = true ∧
    figure.showsObject .spring = true ∧
    figure.showsObject .rigidSupport = true ∧
    figure.showsObject .horizontalTable = true ∧
    figure.isLeftOf .bullet .block = true ∧
    figure.isLeftOf .block .rigidSupport = true ∧
    figure.showsLabel .bulletMass_m = true ∧
    figure.showsLabel .blockMass_M = true ∧
    figure.showsLabel .springConstant_k = true ∧
    figure.showsLabel .bulletVelocity_v = true

/-! ## Physical setup, source data, and governing laws -/

/-!
All physical quantities required by the two-stage model.  The amplitude is
an unconstrained physical length here; no field assigns it the numerical
answer.  `oscillatorSIReadout` packages the post-impact composite mass and
spring stiffness in Physlib's classical harmonic-oscillator model once the
model bridge below is supplied.
-/
structure BallisticSpringSetup where
  bulletMass : MassQuantity
  blockMass : MassQuantity
  springStiffness : SpringStiffnessQuantity
  initialBulletSpeed : SpeedQuantity
  initialBlockSpeed : SpeedQuantity
  postImpactCompositeSpeed : SpeedQuantity
  compositeSpeedAtAmplitude : SpeedQuantity
  springCompressionAtEmbedding : LengthQuantity
  oscillationAmplitude : LengthQuantity
  surfaceCondition : SurfaceCondition
  collisionOutcome : CollisionOutcome
  figure : BallisticSpringFigure
  oscillatorSIReadout : ClassicalMechanics.HarmonicOscillator

/-- Numerical measurements stated in the problem. -/
structure MatchesProblemReadouts (setup : BallisticSpringSetup) : Prop where
  bulletMassGrams : massInGrams setup.bulletMass = 19 / 2
  blockMassKilograms : massInKilograms setup.blockMass = 27 / 5
  springStiffnessNewtonsPerMeter :
    stiffnessInNewtonsPerMeter setup.springStiffness = 6000
  initialBulletSpeedMetersPerSecond :
    speedInMetersPerSecond setup.initialBulletSpeed = 630

/-!
Initial and turning-point conditions.  The zero spring displacement records
the stated assumption that compression is negligible until embedding is
complete.  At the oscillation amplitude the composite is instantaneously at
rest.
-/
structure MatchesBoundaryConditions (setup : BallisticSpringSetup) : Prop where
  blockInitiallyAtRest :
    speedInMetersPerSecond setup.initialBlockSpeed = 0
  springUncompressedWhenEmbeddingCompletes :
    lengthInMeters setup.springCompressionAtEmbedding = 0
  compositeAtRestAtAmplitude :
    speedInMetersPerSecond setup.compositeSpeedAtAmplitude = 0

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalParameters (setup : BallisticSpringSetup) : Prop where
  bulletMassPositive : 0 < massInKilograms setup.bulletMass
  blockMassPositive : 0 < massInKilograms setup.blockMass
  springStiffnessPositive :
    0 < stiffnessInNewtonsPerMeter setup.springStiffness
  initialBulletSpeedPositive :
    0 < speedInMetersPerSecond setup.initialBulletSpeed
  postImpactCompositeSpeedPositive :
    0 < speedInMetersPerSecond setup.postImpactCompositeSpeed
  oscillationAmplitudePositive :
    0 < lengthInMeters setup.oscillationAmplitude

/-!
One-dimensional momentum conservation during the short perfectly inelastic
collision.  The spring impulse is neglected during this stage, as stipulated
in the problem.  The balance is required in every coherent choice of mass,
length, and time units.
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
Bridge from the dimensionful setup to Physlib's one-dimensional classical
harmonic oscillator.  It states only the generic post-impact composite mass
and spring stiffness; it contains no amplitude value or answer choice.
-/
structure SatisfiesPostImpactHarmonicOscillatorModel
    (setup : BallisticSpringSetup) : Prop where
  oscillatorMassIsCompositeMass :
    setup.oscillatorSIReadout.m =
      massInKilograms setup.bulletMass + massInKilograms setup.blockMass
  oscillatorSpringConstantIsStiffness :
    setup.oscillatorSIReadout.k =
      stiffnessInNewtonsPerMeter setup.springStiffness

/-!
Mechanical-energy conservation after embedding, from the initially
uncompressed configuration to the amplitude turning point.  Multiplication
by two removes the common `1/2` factors from kinetic and spring potential
energy.  Energy is deliberately not assumed conserved across the inelastic
collision.
-/
structure SatisfiesEnergyConservationAfterEmbedding
    (setup : BallisticSpringSetup) : Prop where
  energyBalance :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      (massReadout massUnit setup.bulletMass +
          massReadout massUnit setup.blockMass) *
            speedReadout lengthUnit timeUnit
              setup.postImpactCompositeSpeed ^ 2 +
        stiffnessReadout massUnit timeUnit setup.springStiffness *
            lengthReadout lengthUnit setup.springCompressionAtEmbedding ^ 2 =
      (massReadout massUnit setup.bulletMass +
          massReadout massUnit setup.blockMass) *
            speedReadout lengthUnit timeUnit
              setup.compositeSpeedAtAmplitude ^ 2 +
        stiffnessReadout massUnit timeUnit setup.springStiffness *
            lengthReadout lengthUnit setup.oscillationAmplitude ^ 2

/-!
Eliminating the intermediate composite speed gives the generic squared
amplitude relation.  This is a derived conclusion, not a premise.
-/
lemma oscillationAmplitude_squared_relation
    (setup : BallisticSpringSetup)
    (hBoundary : MatchesBoundaryConditions setup)
    (hMomentum : SatisfiesCollisionMomentumConservation setup)
    (hEnergy : SatisfiesEnergyConservationAfterEmbedding setup) :
    stiffnessInNewtonsPerMeter setup.springStiffness *
        lengthInMeters setup.oscillationAmplitude ^ 2 =
      massInKilograms setup.bulletMass ^ 2 *
          speedInMetersPerSecond setup.initialBulletSpeed ^ 2 /
        (massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) := by
  have hMomentumSI := hMomentum.momentumBalance
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    massInKilograms setup.bulletMass *
          speedInMetersPerSecond setup.initialBulletSpeed +
        massInKilograms setup.blockMass *
          speedInMetersPerSecond setup.initialBlockSpeed =
      (massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass) *
        speedInMetersPerSecond setup.postImpactCompositeSpeed at hMomentumSI
  rw [hBoundary.blockInitiallyAtRest] at hMomentumSI
  norm_num at hMomentumSI
  have hEnergySI := hEnergy.energyBalance
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    (massInKilograms setup.bulletMass +
        massInKilograms setup.blockMass) *
          speedInMetersPerSecond setup.postImpactCompositeSpeed ^ 2 +
      stiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters setup.springCompressionAtEmbedding ^ 2 =
    (massInKilograms setup.bulletMass +
        massInKilograms setup.blockMass) *
          speedInMetersPerSecond setup.compositeSpeedAtAmplitude ^ 2 +
      stiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters setup.oscillationAmplitude ^ 2 at hEnergySI
  rw [hBoundary.springUncompressedWhenEmbeddingCompletes,
    hBoundary.compositeAtRestAtAmplitude] at hEnergySI
  norm_num at hEnergySI
  by_cases hTotal :
      massInKilograms setup.bulletMass +
          massInKilograms setup.blockMass = 0
  · rw [hTotal] at hEnergySI ⊢
    norm_num at hEnergySI ⊢
    rcases hEnergySI with hStiffness | hAmplitude
    · simp [hStiffness]
    · simp [hAmplitude]
  · apply (eq_div_iff hTotal).2
    calc
      stiffnessInNewtonsPerMeter setup.springStiffness *
            lengthInMeters setup.oscillationAmplitude ^ 2 *
          (massInKilograms setup.bulletMass +
            massInKilograms setup.blockMass) =
          (massInKilograms setup.bulletMass +
            massInKilograms setup.blockMass) *
            ((massInKilograms setup.bulletMass +
                massInKilograms setup.blockMass) *
              speedInMetersPerSecond setup.postImpactCompositeSpeed ^ 2) := by
                rw [hEnergySI]
                ring
      _ = ((massInKilograms setup.bulletMass +
              massInKilograms setup.blockMass) *
            speedInMetersPerSecond setup.postImpactCompositeSpeed) ^ 2 := by
              ring
      _ = (massInKilograms setup.bulletMass *
            speedInMetersPerSecond setup.initialBulletSpeed) ^ 2 := by
              rw [← hMomentumSI]
      _ = massInKilograms setup.bulletMass ^ 2 *
            speedInMetersPerSecond setup.initialBulletSpeed ^ 2 := by
              ring

/-!
Substitution of the source data and selection of the positive square root
give the exact SI amplitude.  The displayed decimal answer is obtained only
after rounding this expression.
-/
lemma oscillationAmplitude_exact_readout
    (setup : BallisticSpringSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hBoundary : MatchesBoundaryConditions setup)
    (hPhysical : HasPhysicalParameters setup)
    (hMomentum : SatisfiesCollisionMomentumConservation setup)
    (hEnergy : SatisfiesEnergyConservationAfterEmbedding setup) :
    lengthInMeters setup.oscillationAmplitude =
      ((19 / 2000 : ℝ) * 630) /
        Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) := by
  have hMassConversion :
      massInGrams setup.bulletMass =
        1000 * massInKilograms setup.bulletMass := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (setup.bulletMass.2 UnitChoices.SI
        {UnitChoices.SI with mass := MassUnit.grams})
    norm_num [massInGrams, massInKilograms, massReadout,
      UnitChoices.dimScale, M𝓭, MassUnit.grams, MassUnit.kilograms,
      MassUnit.scale, MassUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hBulletMassKilograms :
      massInKilograms setup.bulletMass = (19 / 2000 : ℝ) := by
    rw [hReadouts.bulletMassGrams] at hMassConversion
    norm_num at hMassConversion ⊢
    linarith
  have hSquared := oscillationAmplitude_squared_relation
    setup hBoundary hMomentum hEnergy
  rw [hReadouts.springStiffnessNewtonsPerMeter,
    hBulletMassKilograms, hReadouts.initialBulletSpeedMetersPerSecond,
    hReadouts.blockMassKilograms] at hSquared
  have hTotalNonzero :
      ((27 / 5 : ℝ) + 19 / 2000) ≠ 0 := by
    norm_num
  have hPolynomial :
      (6000 * ((27 / 5 : ℝ) + 19 / 2000)) *
          lengthInMeters setup.oscillationAmplitude ^ 2 =
        ((19 / 2000 : ℝ) * 630) ^ 2 := by
    calc
      (6000 * ((27 / 5 : ℝ) + 19 / 2000)) *
            lengthInMeters setup.oscillationAmplitude ^ 2 =
          ((27 / 5 : ℝ) + 19 / 2000) *
            (6000 * lengthInMeters setup.oscillationAmplitude ^ 2) := by
              ring
      _ = ((27 / 5 : ℝ) + 19 / 2000) *
            (((19 / 2000 : ℝ) ^ 2 * 630 ^ 2) /
              ((19 / 2000 : ℝ) + 27 / 5)) := by
                rw [hSquared]
      _ = (19 / 2000 : ℝ) ^ 2 * 630 ^ 2 := by
            field_simp [hTotalNonzero]
            ring
      _ = ((19 / 2000 : ℝ) * 630) ^ 2 := by
            ring
  have hRadicandPositive :
      0 < (6000 * ((27 / 5 : ℝ) + 19 / 2000)) := by
    norm_num
  have hRootPositive :
      0 < Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) :=
    Real.sqrt_pos.2 hRadicandPositive
  have hRootSquare :
      Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) ^ 2 =
        6000 * ((27 / 5 : ℝ) + 19 / 2000) :=
    Real.sq_sqrt (le_of_lt hRadicandPositive)
  have hProductSquare :
      (lengthInMeters setup.oscillationAmplitude *
          Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000))) ^ 2 =
        ((19 / 2000 : ℝ) * 630) ^ 2 := by
    calc
      (lengthInMeters setup.oscillationAmplitude *
          Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000))) ^ 2 =
        lengthInMeters setup.oscillationAmplitude ^ 2 *
          Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) ^ 2 := by
            ring
      _ = lengthInMeters setup.oscillationAmplitude ^ 2 *
          (6000 * ((27 / 5 : ℝ) + 19 / 2000)) := by
            rw [hRootSquare]
      _ = ((19 / 2000 : ℝ) * 630) ^ 2 := by
            rw [mul_comm]
            exact hPolynomial
  have hFactorization :
      (lengthInMeters setup.oscillationAmplitude *
            Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) -
          (19 / 2000 : ℝ) * 630) *
        (lengthInMeters setup.oscillationAmplitude *
            Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) +
          (19 / 2000 : ℝ) * 630) = 0 := by
    calc
      _ = (lengthInMeters setup.oscillationAmplitude *
              Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000))) ^ 2 -
            ((19 / 2000 : ℝ) * 630) ^ 2 := by
              ring
      _ = 0 := by rw [hProductSquare]; ring
  have hProduct :
      lengthInMeters setup.oscillationAmplitude *
          Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) =
        (19 / 2000 : ℝ) * 630 := by
    rcases mul_eq_zero.mp hFactorization with hEqual | hImpossible
    · linarith
    · exfalso
      nlinarith [hPhysical.oscillationAmplitudePositive]
  apply (eq_div_iff (ne_of_gt hRootPositive)).2
  exact hProduct

/-! ## Displayed answer choices and final target -/

/-- Labels attached to the four amplitudes printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed answer amplitudes, read in metres. -/
def displayedAmplitudeInMeters : AnswerChoice → ℝ
  | .A => 28 / 1000
  | .B => 31 / 1000
  | .C => 33 / 1000
  | .D => 36 / 1000

/-- The dataset's recorded answer label; this metadata is not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- Agreement with a displayed amplitude after rounding to the nearest millimetre. -/
def RoundsToNearestMillimeter
    (amplitude : LengthQuantity) (displayedMeters : ℝ) : Prop :=
  |lengthInMeters amplitude - displayedMeters| < (1 / 2000 : ℝ)

/-- The setup's physical amplitude rounds to the number printed by a choice. -/
def MatchesAnswerChoice
    (setup : BallisticSpringSetup) (choice : AnswerChoice) : Prop :=
  RoundsToNearestMillimeter setup.oscillationAmplitude
    (displayedAmplitudeInMeters choice)

/-- The selected displayed amplitude is strictly closer than every other choice. -/
def IsUniqueClosestDisplayedChoice
    (setup : BallisticSpringSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInMeters setup.oscillationAmplitude -
        displayedAmplitudeInMeters choice| <
      |lengthInMeters setup.oscillationAmplitude -
        displayedAmplitudeInMeters other|

/-!
Momentum conservation gives the composite speed immediately after embedding;
energy conservation during the later undamped spring motion then gives an
amplitude of approximately `0.0332 m`.  It rounds to `3.3 × 10⁻² m`, choice C.

This is the formal target corresponding to
`thm:physics:phyx_mini_0260:target`.  Neither `0.033 m`, answer C, nor a
problem-specific amplitude interval appears in any premise or governing-law
field.
-/
theorem problem_phyx_mini_0260
    (setup : BallisticSpringSetup)
    (hReadouts : MatchesProblemReadouts setup)
    (hBoundary : MatchesBoundaryConditions setup)
    (hScenario : MatchesScenarioAndSuppliedFigure
      setup.surfaceCondition setup.collisionOutcome setup.figure)
    (hPhysical : HasPhysicalParameters setup)
    (hMomentum : SatisfiesCollisionMomentumConservation setup)
    (hOscillator : SatisfiesPostImpactHarmonicOscillatorModel setup)
    (hEnergy : SatisfiesEnergyConservationAfterEmbedding setup) :
    RoundsToNearestMillimeter setup.oscillationAmplitude (33 / 1000) ∧
      MatchesAnswerChoice setup .C ∧
      IsUniqueClosestDisplayedChoice setup .C := by
  have hExact := oscillationAmplitude_exact_readout
    setup hReadouts hBoundary hPhysical hMomentum hEnergy
  have hRadicandPositive :
      0 < (6000 * ((27 / 5 : ℝ) + 19 / 2000)) := by
    norm_num
  have hRootPositive :
      0 < Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) :=
    Real.sqrt_pos.2 hRadicandPositive
  have hRootSquare :
      Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) ^ 2 =
        6000 * ((27 / 5 : ℝ) + 19 / 2000) :=
    Real.sq_sqrt (le_of_lt hRadicandPositive)
  have hLowerSquare :
      ((13 / 400 : ℝ) *
          Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000))) ^ 2 <
        ((19 / 2000 : ℝ) * 630) ^ 2 := by
    rw [mul_pow, hRootSquare]
    norm_num
  have hLowerProduct :
      (13 / 400 : ℝ) *
          Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) <
        (19 / 2000 : ℝ) * 630 := by
    exact (sq_lt_sq₀
      (mul_nonneg (by norm_num) (le_of_lt hRootPositive))
      (by norm_num)).mp hLowerSquare
  have hLower :
      (13 / 400 : ℝ) <
        lengthInMeters setup.oscillationAmplitude := by
    rw [hExact]
    exact (lt_div_iff₀ hRootPositive).2 hLowerProduct
  have hUpperSquare :
      ((19 / 2000 : ℝ) * 630) ^ 2 <
        ((67 / 2000 : ℝ) *
          Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000))) ^ 2 := by
    calc
      ((19 / 2000 : ℝ) * 630) ^ 2 <
          (67 / 2000 : ℝ) ^ 2 *
            (6000 * ((27 / 5 : ℝ) + 19 / 2000)) := by
              norm_num
      _ = ((67 / 2000 : ℝ) *
            Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000))) ^ 2 := by
              rw [mul_pow, hRootSquare]
  have hUpperProduct :
      (19 / 2000 : ℝ) * 630 <
        (67 / 2000 : ℝ) *
          Real.sqrt (6000 * ((27 / 5 : ℝ) + 19 / 2000)) := by
    exact (sq_lt_sq₀
      (by norm_num)
      (mul_nonneg (by norm_num) (le_of_lt hRootPositive))).mp hUpperSquare
  have hUpper :
      lengthInMeters setup.oscillationAmplitude <
        (67 / 2000 : ℝ) := by
    rw [hExact]
    exact (div_lt_iff₀ hRootPositive).2 hUpperProduct
  have hRounding :
      RoundsToNearestMillimeter setup.oscillationAmplitude
        (33 / 1000) := by
    unfold RoundsToNearestMillimeter
    apply abs_lt.mpr
    constructor <;> linarith
  refine ⟨hRounding, ?_, ?_⟩
  · simpa [MatchesAnswerChoice, displayedAmplitudeInMeters] using hRounding
  · intro other hOther
    cases other
    · change
        |lengthInMeters setup.oscillationAmplitude - 33 / 1000| <
          |lengthInMeters setup.oscillationAmplitude - 28 / 1000|
      have hDistancePositive :
          0 < lengthInMeters setup.oscillationAmplitude - 28 / 1000 := by
        linarith
      rw [abs_of_pos hDistancePositive]
      unfold RoundsToNearestMillimeter at hRounding
      linarith
    · change
        |lengthInMeters setup.oscillationAmplitude - 33 / 1000| <
          |lengthInMeters setup.oscillationAmplitude - 31 / 1000|
      have hDistancePositive :
          0 < lengthInMeters setup.oscillationAmplitude - 31 / 1000 := by
        linarith
      rw [abs_of_pos hDistancePositive]
      unfold RoundsToNearestMillimeter at hRounding
      linarith
    · exact (hOther rfl).elim
    · change
        |lengthInMeters setup.oscillationAmplitude - 33 / 1000| <
          |lengthInMeters setup.oscillationAmplitude - 36 / 1000|
      have hDistanceNegative :
          lengthInMeters setup.oscillationAmplitude - 36 / 1000 < 0 := by
        linarith
      rw [abs_of_neg hDistanceNegative]
      unfold RoundsToNearestMillimeter at hRounding
      linarith

end PhyXMiniProblems.ProblemPhyXMini0260
