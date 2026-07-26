import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.Units.WithDim.Basic

/-!
# Maximum non-slip amplitude for two stacked blocks

This file models problem `phyx_mini_0231`.  A large block `P`, attached to a
light spring, moves horizontally in simple harmonic motion on a frictionless
surface.  A smaller block `B` rests on top of `P` and is accelerated only by
static friction.

Mass, length, frequency, acceleration, force, and spring stiffness are
represented by Physlib dimensionful quantities.  The coefficient of static
friction is a dimensionless real readout.  Physlib's scalar harmonic
oscillator is connected explicitly to coherent SI readouts of the physical
system.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0231

open Dimension

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical length, used in particular for an oscillation amplitude. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical cyclic frequency, carrying the inverse-time dimension. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical acceleration, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A physical force, with dimension mass times acceleration. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A spring stiffness, equivalently force per length or mass per time squared. -/
abbrev StiffnessQuantity : Type :=
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

/-- Read a physical cyclic frequency in hertz. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Read a physical acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Read a physical force in newtons. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- Read a physical spring stiffness in newtons per metre. -/
def stiffnessInNewtonsPerMeter (stiffness : StiffnessQuantity) : ℝ :=
  (stiffness UnitChoices.SI).val

/-- Construct a physical length from its metre readout. -/
def lengthOfMeters (value : ℝ) : LengthQuantity :=
  CarriesDimension.toDimensionful UnitChoices.SI ⟨value⟩

/-! ## Physical objects and primary-figure labels -/

/-- The two block labels printed in the primary figure. -/
inductive BlockLabel where
  | P
  | B
  deriving DecidableEq, Repr

/-- The relative block sizes visible in the primary figure. -/
inductive BlockSize where
  | large
  | small
  deriving DecidableEq, Repr

/-- The vertical/support placement of a block in the primary figure. -/
inductive BlockPlacement where
  | onHorizontalSurface
  | onTopOfP
  deriving DecidableEq, Repr

/-- The attachment represented by the spring drawn between the wall and `P`. -/
inductive SpringAttachment where
  | wallToBlockP
  deriving DecidableEq, Repr

/-- The stated condition of the horizontal support beneath block `P`. -/
inductive SurfaceCondition where
  | horizontalFrictionless
  deriving DecidableEq, Repr

/-- The stated idealization of the spring. -/
inductive SpringIdealization where
  | light
  deriving DecidableEq, Repr

/-!
The complete physical setup.

The force and acceleration fields are physical response quantities, indexed
by a proposed amplitude where appropriate.  Their relation to SHM, Newton's
second law, vertical force balance, and Coulomb static friction is supplied
separately by `SatisfiesHorizontalSHMAndStaticFrictionLaws`.
-/
structure StackedSpringBlocksSetup where
  blockMass : BlockLabel → MassQuantity
  blockSize : BlockLabel → BlockSize
  blockPlacement : BlockLabel → BlockPlacement
  springMass : MassQuantity
  springStiffness : StiffnessQuantity
  oscillationFrequency : FrequencyQuantity
  staticFrictionCoefficient : ℝ
  gravitationalAcceleration : AccelerationQuantity
  supportOscillator : ClassicalMechanics.HarmonicOscillator
  peakHorizontalAcceleration : LengthQuantity → AccelerationQuantity
  normalForceOnB : ForceQuantity
  maximumStaticFrictionForce : ForceQuantity
  requiredStaticFrictionForce : LengthQuantity → ForceQuantity
  springAttachment : SpringAttachment
  surfaceCondition : SurfaceCondition
  springIdealization : SpringIdealization

/-!
The scalar data and qualitative geometry supplied by the problem and its
primary image.  The gravitational acceleration is the standard near-Earth
calibration `9.80 m/s²` used by the recorded multiple-choice calculation.
This predicate contains no proposed maximum amplitude.
-/
def MatchesProblemAndFigureData (setup : StackedSpringBlocksSetup) : Prop :=
  frequencyInHertz setup.oscillationFrequency = 3 / 2 ∧
    setup.staticFrictionCoefficient = 3 / 5 ∧
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5 ∧
    massInKilograms setup.springMass = 0 ∧
    setup.blockSize .P = .large ∧
    setup.blockSize .B = .small ∧
    setup.blockPlacement .P = .onHorizontalSurface ∧
    setup.blockPlacement .B = .onTopOfP ∧
    setup.springAttachment = .wallToBlockP ∧
    setup.surfaceCondition = .horizontalFrictionless ∧
    setup.springIdealization = .light

/-- Positivity conditions for the masses and other physical magnitudes. -/
def HasPhysicalParameters (setup : StackedSpringBlocksSetup) : Prop :=
  0 < massInKilograms (setup.blockMass .P) ∧
    0 < massInKilograms (setup.blockMass .B) ∧
    0 < stiffnessInNewtonsPerMeter setup.springStiffness ∧
    0 < frequencyInHertz setup.oscillationFrequency ∧
    0 ≤ setup.staticFrictionCoefficient ∧
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-! ## Governing SHM, Newtonian, and static-friction laws -/

/-!
The governing laws for the stacked-block motion.

* Since `B` does not slip relative to `P`, the oscillator's effective mass is
  the sum of the two block masses, while the light spring supplies the stated
  stiffness.
* Cyclic frequency and angular frequency obey `ω = 2πf`.
* A nonnegative SHM amplitude `A` has peak acceleration `ω² A`.
* Vertical force balance gives `N = m_B g`.
* Coulomb static friction is bounded by `μ_s N`.
* The horizontal friction required to carry `B` is `m_B a_peak`.

Every field is a general physical law or adapter.  None states which amplitude
is maximal or mentions a displayed answer.
-/
structure SatisfiesHorizontalSHMAndStaticFrictionLaws
    (setup : StackedSpringBlocksSetup) : Prop where
  oscillator_effective_mass :
    setup.supportOscillator.m =
      massInKilograms (setup.blockMass .P) +
        massInKilograms (setup.blockMass .B)
  oscillator_spring_stiffness :
    setup.supportOscillator.k =
      stiffnessInNewtonsPerMeter setup.springStiffness
  angular_frequency_from_cyclic_frequency :
    setup.supportOscillator.ω =
      2 * Real.pi * frequencyInHertz setup.oscillationFrequency
  shm_peak_acceleration :
    ∀ amplitude : LengthQuantity,
      0 ≤ lengthInMeters amplitude →
      accelerationInMetersPerSecondSquared
          (setup.peakHorizontalAcceleration amplitude) =
        setup.supportOscillator.ω ^ 2 * lengthInMeters amplitude
  vertical_force_balance :
    forceInNewtons setup.normalForceOnB =
      massInKilograms (setup.blockMass .B) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  coulomb_static_friction_limit :
    forceInNewtons setup.maximumStaticFrictionForce =
      setup.staticFrictionCoefficient *
        forceInNewtons setup.normalForceOnB
  newton_second_law_for_blockB :
    ∀ amplitude : LengthQuantity,
      0 ≤ lengthInMeters amplitude →
      forceInNewtons (setup.requiredStaticFrictionForce amplitude) =
        massInKilograms (setup.blockMass .B) *
          accelerationInMetersPerSecondSquared
            (setup.peakHorizontalAcceleration amplitude)

/-!
At a proposed nonnegative amplitude, block `B` does not slip when the required
horizontal friction does not exceed the available static-friction magnitude.
-/
def DoesNotSlipAtAmplitude
    (setup : StackedSpringBlocksSetup) (amplitude : LengthQuantity) : Prop :=
  0 ≤ lengthInMeters amplitude ∧
    forceInNewtons (setup.requiredStaticFrictionForce amplitude) ≤
      forceInNewtons setup.maximumStaticFrictionForce

/-!
An amplitude is the requested maximum when it is non-slipping and every other
non-slipping physical amplitude has no larger metre readout.
-/
def IsMaximumNonSlipAmplitude
    (setup : StackedSpringBlocksSetup) (amplitude : LengthQuantity) : Prop :=
  DoesNotSlipAtAmplitude setup amplitude ∧
    ∀ other : LengthQuantity,
      DoesNotSlipAtAmplitude setup other →
      lengthInMeters other ≤ lengthInMeters amplitude

/-!
The governing laws imply the usual threshold formula
`A_max = μ_s g / (2πf)²`.  This is a derived conclusion, not a field of the
law structure.
-/
lemma maximumNonSlipAmplitude_formula
    (setup : StackedSpringBlocksSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesHorizontalSHMAndStaticFrictionLaws setup)
    (maximumAmplitude : LengthQuantity)
    (h_maximum : IsMaximumNonSlipAmplitude setup maximumAmplitude) :
    lengthInMeters maximumAmplitude =
      setup.staticFrictionCoefficient *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration /
        (2 * Real.pi * frequencyInHertz setup.oscillationFrequency) ^ 2 := by
  rcases h_physical with ⟨h_massP, h_massB, h_stiffness, h_frequency,
    h_friction, h_gravity⟩
  rcases h_maximum with ⟨h_maximum_nonslip, h_greatest⟩
  let threshold : ℝ :=
    setup.staticFrictionCoefficient *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration /
      (2 * Real.pi * frequencyInHertz setup.oscillationFrequency) ^ 2
  have h_angular_frequency :
      0 < 2 * Real.pi * frequencyInHertz setup.oscillationFrequency := by
    positivity
  have h_angular_frequency_sq :
      0 < (2 * Real.pi * frequencyInHertz setup.oscillationFrequency) ^ 2 := by
    positivity
  have h_threshold_nonnegative : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have h_read_lengthOfMeters (value : ℝ) :
      lengthInMeters (lengthOfMeters value) = value := by
    simp [lengthInMeters, lengthOfMeters,
      CarriesDimension.toDimensionful_apply_apply]
  have h_maximum_le_threshold :
      lengthInMeters maximumAmplitude ≤ threshold := by
    have h_peak := h_laws.shm_peak_acceleration maximumAmplitude
      h_maximum_nonslip.1
    have h_newton := h_laws.newton_second_law_for_blockB maximumAmplitude
      h_maximum_nonslip.1
    have h_force_limit := h_maximum_nonslip.2
    rw [h_newton, h_peak, h_laws.angular_frequency_from_cyclic_frequency,
      h_laws.coulomb_static_friction_limit, h_laws.vertical_force_balance] at h_force_limit
    have h_cancelled :
        (2 * Real.pi * frequencyInHertz setup.oscillationFrequency) ^ 2 *
            lengthInMeters maximumAmplitude ≤
          setup.staticFrictionCoefficient *
            accelerationInMetersPerSecondSquared setup.gravitationalAcceleration := by
      apply le_of_mul_le_mul_left (a :=
        massInKilograms (setup.blockMass .B)) (a0 := h_massB)
      nlinarith [h_force_limit]
    exact (le_div_iff₀ h_angular_frequency_sq).2 (by
      simpa [threshold, mul_comm] using h_cancelled)
  have h_threshold_nonslip :
      DoesNotSlipAtAmplitude setup (lengthOfMeters threshold) := by
    constructor
    · simpa [h_read_lengthOfMeters] using h_threshold_nonnegative
    · have h_peak := h_laws.shm_peak_acceleration (lengthOfMeters threshold)
        (by simpa [h_read_lengthOfMeters] using h_threshold_nonnegative)
      have h_newton :=
        h_laws.newton_second_law_for_blockB (lengthOfMeters threshold)
          (by simpa [h_read_lengthOfMeters] using h_threshold_nonnegative)
      rw [h_newton, h_peak, h_laws.angular_frequency_from_cyclic_frequency,
        h_laws.coulomb_static_friction_limit, h_laws.vertical_force_balance,
        h_read_lengthOfMeters]
      dsimp [threshold]
      field_simp [ne_of_gt h_angular_frequency_sq]
      exact le_rfl
  have h_threshold_le_maximum :
      threshold ≤ lengthInMeters maximumAmplitude := by
    simpa [h_read_lengthOfMeters] using
      h_greatest (lengthOfMeters threshold) h_threshold_nonslip
  exact le_antisymm h_maximum_le_threshold h_threshold_le_maximum

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
  | .A => 158 / 25
  | .B => 321 / 50
  | .C => 163 / 25
  | .D => 331 / 50

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a displayed answer to the nearest `0.01 cm`.  The half-step
tolerance makes the conclusion a rounding statement rather than the false
claim that the expression involving `π` is exactly a terminating decimal.
-/
def MatchesAnswerChoice
    (amplitude : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters amplitude - choice.centimeters| ≤ 1 / 200

/-!
With `f = 1.50 Hz`, `μ_s = 0.600`, and `g = 9.80 m/s²`, the greatest
amplitude that static friction can transmit rounds to `6.62 cm`, answer D.

This formalizes `thm:physics:phyx_mini_0231:target`.
-/
theorem maximumNonSlipAmplitude_matches_recordedAnswerD
    (setup : StackedSpringBlocksSetup)
    (h_data : MatchesProblemAndFigureData setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesHorizontalSHMAndStaticFrictionLaws setup)
    (maximumAmplitude : LengthQuantity)
    (h_maximum : IsMaximumNonSlipAmplitude setup maximumAmplitude) :
    MatchesAnswerChoice maximumAmplitude recordedAnswerChoice := by
  have h_frequency_data :
      frequencyInHertz setup.oscillationFrequency = 3 / 2 :=
    h_data.1
  have h_friction_data : setup.staticFrictionCoefficient = 3 / 5 :=
    h_data.2.1
  have h_gravity_data :
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
        49 / 5 :=
    h_data.2.2.1
  have h_formula :=
    maximumNonSlipAmplitude_formula setup h_physical h_laws maximumAmplitude
      h_maximum
  change
    |100 * lengthInMeters maximumAmplitude - (331 / 50 : ℝ)| ≤ 1 / 200
  rw [h_formula, h_frequency_data, h_friction_data, h_gravity_data]
  have h_value :
      (100 : ℝ) * ((3 / 5) * (49 / 5) / (2 * Real.pi * (3 / 2)) ^ 2) =
        196 / (3 * Real.pi ^ 2) := by
    field_simp [ne_of_gt Real.pi_pos]
    ring
  rw [h_value]
  have hpi_lower := Real.pi_gt_d4
  have hpi_upper := Real.pi_lt_d4
  norm_num at hpi_lower hpi_upper
  have hpi_sq_lower : ((6283 : ℝ) / 2000) ^ 2 < Real.pi ^ 2 := by
    nlinarith [Real.pi_pos]
  have hpi_sq_upper : Real.pi ^ 2 < ((3927 : ℝ) / 1250) ^ 2 := by
    nlinarith [Real.pi_pos]
  have hdenominator : 0 < 3 * Real.pi ^ 2 := by
    positivity
  have hquotient_lower :
      (1323 : ℝ) / 200 ≤ 196 / (3 * Real.pi ^ 2) := by
    apply (le_div_iff₀ hdenominator).2
    nlinarith [hpi_sq_upper]
  have hquotient_upper :
      196 / (3 * Real.pi ^ 2) ≤ (53 : ℝ) / 8 := by
    apply (div_le_iff₀ hdenominator).2
    nlinarith [hpi_sq_lower]
  rw [abs_le]
  constructor <;> norm_num <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0231
