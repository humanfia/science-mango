import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/-!
# Slip threshold for two stacked blocks attached to a spring

This file models problem `phyx_mini_0258`.  A large block `M` is attached to
an ideal horizontal spring on a frictionless horizontal surface, and a smaller
block `m` rests on top of it.  Static friction accelerates the upper block while
the blocks execute simple harmonic motion together.

Mass, length, acceleration, force, and spring stiffness are represented by
Physlib dimensionful quantities.  Real numbers occur only as coherent SI
readouts, the dimensionless coefficient of static friction, and displayed
answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0258

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical length, used in particular for the oscillation amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical acceleration, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A physical force, with dimension mass times acceleration. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A spring stiffness, equivalently force per length or mass per time squared. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Read a physical force in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- Read a physical spring stiffness in newtons per metre. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  (stiffness UnitChoices.SI).val

/-! ## Physical objects and figure-derived geometry -/

/-- The two mathematical labels printed on the blocks in the primary image. -/
inductive BlockLabel where
  | small_m
  | large_M
  deriving DecidableEq, Repr

/-- Vertically distinguished locations of the two blocks. -/
inductive BlockPlacement where
  | onHorizontalSurface
  | onTopOfLargeBlock
  deriving DecidableEq, Repr

/-- The two endpoints of the spring visible in the image. -/
inductive SpringEndpoint where
  | fixedWall
  | largeBlock
  deriving DecidableEq, Repr

/-- Orientations distinguished by the apparatus. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The stated condition of the support below the large block. -/
inductive SurfaceCondition where
  | horizontalFrictionless
  deriving DecidableEq, Repr

/-- The linear, negligibly massive spring idealization used by the SHM model. -/
inductive SpringIdealization where
  | idealMasslessLinear
  deriving DecidableEq, Repr

/-- The motion regime relevant immediately before relative slipping begins. -/
inductive MotionRegime where
  | simpleHarmonicTogether
  deriving DecidableEq, Repr

/-- The mathematical label printed beside the spring. -/
inductive SpringFigureLabel where
  | stiffness_k
  deriving DecidableEq, Repr

/-- Qualitative geometry read directly from the supplied primary image. -/
structure StackedBlocksSpringFigure where
  smallBlockLabel : BlockLabel
  largeBlockLabel : BlockLabel
  smallBlockPlacement : BlockPlacement
  largeBlockPlacement : BlockPlacement
  springLeftEndpoint : SpringEndpoint
  springRightEndpoint : SpringEndpoint
  springOrientation : Orientation
  springLabel : SpringFigureLabel
  surfaceCondition : SurfaceCondition

/-!
The physical apparatus and its response quantities.

The amplitude-indexed acceleration and friction fields are related to the
apparatus only by the governing-law structure below.  In particular, this
structure assigns no numerical value to the requested threshold amplitude.
-/
structure StackedBlocksSpringSetup where
  blockMass : BlockLabel → MassQuantity
  springStiffness : SpringStiffnessQuantity
  staticFrictionCoefficient : ℝ
  gravitationalAccelerationMagnitude : AccelerationQuantity
  supportOscillator : ClassicalMechanics.HarmonicOscillator
  peakHorizontalAcceleration : LengthQuantity → AccelerationQuantity
  normalForceOnSmallBlock : ForceQuantity
  maximumStaticFrictionForce : ForceQuantity
  requiredStaticFrictionForce : LengthQuantity → ForceQuantity
  springIdealization : SpringIdealization
  motionRegime : MotionRegime
  figure : StackedBlocksSpringFigure

/-!
The numerical givens and qualitative readouts supplied by the problem and its
primary image.  The value `9.80 m/s²` is the standard near-Earth calibration
used for the recorded multiple-choice calculation.  No threshold amplitude or
answer-choice claim occurs here.
-/
structure MatchesProblemAndFigureData
    (setup : StackedBlocksSpringSetup) : Prop where
  smallBlockMassReadout :
    massInKilograms (setup.blockMass .small_m) = 9 / 5
  largeBlockMassReadout :
    massInKilograms (setup.blockMass .large_M) = 10
  springStiffnessReadout :
    springStiffnessInNewtonsPerMeter setup.springStiffness = 200
  staticFrictionCoefficientReadout :
    setup.staticFrictionCoefficient = 2 / 5
  gravitationalAccelerationReadout :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 49 / 5
  smallBlockLabelReadout : setup.figure.smallBlockLabel = .small_m
  largeBlockLabelReadout : setup.figure.largeBlockLabel = .large_M
  smallBlockOnLargeBlock :
    setup.figure.smallBlockPlacement = .onTopOfLargeBlock
  largeBlockOnSupport :
    setup.figure.largeBlockPlacement = .onHorizontalSurface
  springAnchoredToWall : setup.figure.springLeftEndpoint = .fixedWall
  springAttachedToLargeBlock :
    setup.figure.springRightEndpoint = .largeBlock
  horizontalSpring : setup.figure.springOrientation = .horizontal
  springLabelReadout : setup.figure.springLabel = .stiffness_k
  frictionlessHorizontalSupport :
    setup.figure.surfaceCondition = .horizontalFrictionless
  idealSpring : setup.springIdealization = .idealMasslessLinear
  jointSimpleHarmonicMotion : setup.motionRegime = .simpleHarmonicTogether

/-- Positivity and nondegeneracy conditions for the physical parameters. -/
structure HasPhysicalParameters
    (setup : StackedBlocksSpringSetup) : Prop where
  smallBlockMassPositive :
    0 < massInKilograms (setup.blockMass .small_m)
  largeBlockMassPositive :
    0 < massInKilograms (setup.blockMass .large_M)
  springStiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness
  staticFrictionCoefficientNonnegative :
    0 ≤ setup.staticFrictionCoefficient
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude

/-! ## Governing SHM, Newtonian, and static-friction laws -/

/-!
The governing laws for the stacked-block motion.

* Before slipping, both blocks form the effective mass of the ideal spring
  oscillator.
* A nonnegative SHM amplitude `A` has peak acceleration `ω² A`.
* Vertical force balance gives `N = m g` for the upper block.
* Coulomb static friction has limiting magnitude `μ_s N`.
* Newton's second law requires horizontal friction `m a_peak` on the upper
  block.

These are general laws and adapters.  No field states the requested amplitude,
the derived threshold formula, or a displayed answer.
-/
structure SatisfiesStackedBlocksSHMAndFrictionLaws
    (setup : StackedBlocksSpringSetup) : Prop where
  oscillatorEffectiveMass :
    setup.supportOscillator.m =
      massInKilograms (setup.blockMass .large_M) +
        massInKilograms (setup.blockMass .small_m)
  oscillatorSpringStiffness :
    setup.supportOscillator.k =
      springStiffnessInNewtonsPerMeter setup.springStiffness
  shmPeakAcceleration :
    ∀ amplitude : LengthQuantity,
      0 ≤ lengthInMeters amplitude →
      accelerationInMetersPerSecondSquared
          (setup.peakHorizontalAcceleration amplitude) =
        setup.supportOscillator.ω ^ 2 * lengthInMeters amplitude
  verticalForceBalance :
    forceInNewtons setup.normalForceOnSmallBlock =
      massInKilograms (setup.blockMass .small_m) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude
  coulombStaticFrictionLimit :
    forceInNewtons setup.maximumStaticFrictionForce =
      setup.staticFrictionCoefficient *
        forceInNewtons setup.normalForceOnSmallBlock
  newtonSecondLawForSmallBlock :
    ∀ amplitude : LengthQuantity,
      0 ≤ lengthInMeters amplitude →
      forceInNewtons (setup.requiredStaticFrictionForce amplitude) =
        massInKilograms (setup.blockMass .small_m) *
          accelerationInMetersPerSecondSquared
            (setup.peakHorizontalAcceleration amplitude)

/-!
At the verge of slipping, the nonnegative amplitude requires exactly the
maximum static-friction magnitude.  This is the physical threshold condition,
not a numerical specification of which amplitude satisfies it.
-/
def IsAtVergeOfSlipping
    (setup : StackedBlocksSpringSetup) (amplitude : LengthQuantity) : Prop :=
  0 ≤ lengthInMeters amplitude ∧
    forceInNewtons (setup.requiredStaticFrictionForce amplitude) =
      forceInNewtons setup.maximumStaticFrictionForce

/-!
The SHM and friction laws imply
`A = μ_s g (M + m) / k` at the slip threshold.  The upper-block mass cancels
between its required friction and its maximum static friction; the total mass
remains in the oscillator frequency.  This formula is a derived conclusion,
not a governing-law field.
-/
lemma vergeOfSlippingAmplitude_formula
    (setup : StackedBlocksSpringSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesStackedBlocksSHMAndFrictionLaws setup)
    (amplitude : LengthQuantity)
    (h_verge : IsAtVergeOfSlipping setup amplitude) :
    lengthInMeters amplitude =
      setup.staticFrictionCoefficient *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          (massInKilograms (setup.blockMass .large_M) +
            massInKilograms (setup.blockMass .small_m)) /
        springStiffnessInNewtonsPerMeter setup.springStiffness := by
  rcases h_verge with ⟨h_amplitude_nonnegative, h_friction_threshold⟩
  have h_peak_acceleration :=
    h_laws.shmPeakAcceleration amplitude h_amplitude_nonnegative
  have h_required_friction :=
    h_laws.newtonSecondLawForSmallBlock amplitude h_amplitude_nonnegative
  rw [h_required_friction, h_peak_acceleration,
    h_laws.coulombStaticFrictionLimit, h_laws.verticalForceBalance,
    setup.supportOscillator.ω_sq, h_laws.oscillatorSpringStiffness,
    h_laws.oscillatorEffectiveMass] at h_friction_threshold
  have h_total_mass_positive :
      0 <
        massInKilograms (setup.blockMass .large_M) +
          massInKilograms (setup.blockMass .small_m) :=
    add_pos h_physical.largeBlockMassPositive h_physical.smallBlockMassPositive
  field_simp [h_total_mass_positive.ne', h_physical.springStiffnessPositive.ne']
      at h_friction_threshold ⊢
  nlinarith [h_physical.smallBlockMassPositive]

/-! ## Displayed choices and formalization target -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The amplitude in centimetres printed beside each answer label. -/
def AnswerChoice.centimeters : AnswerChoice → ℝ
  | .A => 17
  | .B => 20
  | .C => 23
  | .D => 26

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-!
Agreement with a displayed whole-centimetre answer.  The half-centimetre
tolerance expresses rounding to the nearest centimetre rather than the false
exact assertion that the threshold is exactly `23 cm`.
-/
def MatchesAnswerChoice
    (amplitude : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters amplitude - choice.centimeters| ≤ 1 / 2

/-!
For `m = 1.8 kg`, `M = 10 kg`, `k = 200 N/m`, `μ_s = 0.40`, and
`g = 9.80 m/s²`, the threshold amplitude is `23.128 cm`, which rounds to
`23 cm`, the recorded answer C.

This formalizes `thm:physics:phyx_mini_0258:target`.
-/
theorem vergeOfSlippingAmplitude_matches_recordedAnswerC
    (setup : StackedBlocksSpringSetup)
    (h_data : MatchesProblemAndFigureData setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesStackedBlocksSHMAndFrictionLaws setup)
    (amplitude : LengthQuantity)
    (h_verge : IsAtVergeOfSlipping setup amplitude) :
    MatchesAnswerChoice amplitude recordedAnswerChoice := by
  have h_amplitude :=
    vergeOfSlippingAmplitude_formula setup h_physical h_laws amplitude h_verge
  unfold MatchesAnswerChoice recordedAnswerChoice
  simp only [AnswerChoice.centimeters]
  rw [lengthInCentimeters, h_amplitude,
    h_data.staticFrictionCoefficientReadout,
    h_data.gravitationalAccelerationReadout,
    h_data.largeBlockMassReadout,
    h_data.smallBlockMassReadout,
    h_data.springStiffnessReadout]
  norm_num [abs_of_nonneg]

end PhyXMiniProblems.ProblemPhyXMini0258
