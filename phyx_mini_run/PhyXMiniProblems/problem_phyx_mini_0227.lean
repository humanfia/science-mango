import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Calculus.Deriv.Basic
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/-!
# Period of a meterstick physical pendulum

A negligibly massive rigid rod of length `0.500 m` joins a pivot to one end of
a uniform `1.00 m` meterstick.  The rod and meterstick are
collinear, and the assembly is released from a small angle.  This file models
the assembly as a physical pendulum and compares its small-angle period with
that of a `1.00 m` simple pendulum.

The geometric lengths, masses, acceleration, torques, moments of inertia, and
periods are unit-independent Physlib quantities.  Scalar equations below use
their coherent SI readouts.  The exact nonlinear gravitational torques are
retained as functions of the angular displacement.  The two Physlib harmonic
oscillators represent only their derivatives at the downward equilibrium.

The period of each nonlinear pendulum is represented as a function of positive
oscillation amplitude.  Its right-hand limit as the amplitude tends to zero is
then identified with the period of the corresponding linearized oscillator.
Thus no finite-amplitude nonlinear period is equated exactly to a harmonic
oscillator period.

Assumption/target boundary:

* Figure and problem data specify the component lengths, attachment geometry,
  the negligible support-rod mass, a uniform meterstick, a small release
  angle, and positivity of the physical parameters.
* Governing laws specify the center of mass, the uniform-stick inertia, the
  parallel-axis theorem, the exact sinusoidal gravitational torques, their
  derivatives at equilibrium, and the small-amplitude period limits.
* The limiting period ratio, the direction of its difference, and the reported
  `4.08%` answer are conclusions only.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0227

open Dimension Filter Topology

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A physical length, independent of the unit system used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time interval. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical acceleration, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A scalar moment of inertia about an axis, with dimension mass times length squared. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) ℝ)

/-- A signed torque, with dimension mass times length squared per time squared. -/
abbrev TorqueQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Read a physical time interval in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Read an acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Read a scalar moment of inertia in kilogram metre squared. -/
def momentOfInertiaInKilogramMeterSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  (inertia UnitChoices.SI).val

/-- Read a signed torque in newton metres. -/
def torqueInNewtonMeters (torque : TorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-! ## Apparatus and figure labels -/

/-- The two labeled ends of the very light suspension rod. -/
inductive SuspensionRodEnd where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The two distinguished ends of the meterstick. -/
inductive MeterstickEnd where
  | rodSide
  | freeSide
  deriving DecidableEq, Repr

/-- Relative axial arrangement of the support rod and meterstick. -/
inductive ComponentAlignment where
  | collinear
  | noncollinear
  deriving DecidableEq, Repr

/-- Reference direction from which the release angle is measured. -/
inductive AngleReferenceDirection where
  | downwardVertical
  deriving DecidableEq, Repr

/-- The mass-distribution idealization used for the meterstick. -/
inductive StickMassDistribution where
  | uniformAlongLength
  | unspecified
  deriving DecidableEq, Repr

/--
All physical quantities and labeled geometric features used in the comparison.

For each pendulum, the gravitational-torque field describes the exact
nonlinear signed torque law and the amplitude-indexed period field describes
the nonlinear period for positive angular amplitudes.  The oscillator is only
the model obtained from the negative derivative of that torque at equilibrium,
while the distinguished period is the right-hand zero-amplitude limit.  No
requested period ratio or percentage difference is stored here.
-/
structure MeterstickPendulumSetup where
  suspensionRodLength : LengthQuantity
  suspensionRodMass : MassQuantity
  meterstickLength : LengthQuantity
  meterstickMass : MassQuantity
  meterstickMassDistribution : StickMassDistribution
  pivotRodEnd : SuspensionRodEnd
  junctionRodEnd : SuspensionRodEnd
  junctionMeterstickEnd : MeterstickEnd
  rodAndMeterstickAlignment : ComponentAlignment
  releaseAngleRadians : ℝ
  releaseAngleReference : AngleReferenceDirection
  releaseIsInSmallAngleRegime : Prop
  centerOfMassDistanceFromPivot : LengthQuantity
  meterstickInertiaAboutCenter : MomentOfInertiaQuantity
  assemblyInertiaAboutPivot : MomentOfInertiaQuantity
  gravitationalAccelerationMagnitude : AccelerationQuantity
  physicalPendulumGravitationalTorque : ℝ → TorqueQuantity
  physicalPendulumPeriodAtAmplitude : ℝ → TimeQuantity
  physicalPendulumOscillator : ClassicalMechanics.HarmonicOscillator
  physicalPendulumSmallAmplitudePeriod : TimeQuantity
  referencePendulumLength : LengthQuantity
  referenceBobMass : MassQuantity
  referencePendulumGravitationalTorque : ℝ → TorqueQuantity
  referencePendulumPeriodAtAmplitude : ℝ → TimeQuantity
  referencePendulumOscillator : ClassicalMechanics.HarmonicOscillator
  referencePendulumSmallAmplitudePeriod : TimeQuantity

/--
Primary-figure readouts and attachment geometry.  The image labels the support
rod as `0.500 m`, places the pivot at its upper end, and shows the meterstick
attached at the lower end in the same straight line.  Calling the ruled body a
meterstick supplies its `1.00 m` length; the source does not specify which
numbered mark is at the junction, so the end is labeled only as `rodSide`.
-/
def MatchesMeterstickPendulumFigure
    (setup : MeterstickPendulumSetup) : Prop :=
  lengthInMeters setup.suspensionRodLength = 1 / 2 ∧
    lengthInMeters setup.meterstickLength = 1 ∧
    setup.pivotRodEnd = .upper ∧
    setup.junctionRodEnd = .lower ∧
    setup.junctionMeterstickEnd = .rodSide ∧
    setup.rodAndMeterstickAlignment = .collinear

/--
Textual data and standard idealizations.  “Very light” is modeled by zero
support-rod mass, while the meterstick is treated as uniform.  The proposition
`releaseIsInSmallAngleRegime` retains the source's qualitative small-angle
condition without imposing an arbitrary numerical cutoff.
-/
def HasMeterstickPendulumProblemData
    (setup : MeterstickPendulumSetup) : Prop :=
  massInKilograms setup.suspensionRodMass = 0 ∧
    setup.meterstickMassDistribution = .uniformAlongLength ∧
    setup.releaseAngleReference = .downwardVertical ∧
    setup.releaseIsInSmallAngleRegime ∧
    lengthInMeters setup.referencePendulumLength = 1 ∧
    0 < massInKilograms setup.meterstickMass ∧
    0 < massInKilograms setup.referenceBobMass ∧
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude

/-! ## Governing physical laws -/

/--
The uniform-meterstick, parallel-axis, nonlinear gravitational-restoring, and
small-amplitude period-limit laws used in the calculation.

With positive angle chosen away from the downward vertical, the exact signed
gravitational torques are `-M g d sin θ` and `-m g L sin θ`.  The negatives of
their derivatives at the downward equilibrium supply the `k` coefficients of
the linearized oscillators.  For the physical pendulum, the generalized
inertia is `I_p`; for the simple-pendulum comparison it is `m L²`.  The
reference bob mass is deliberately retained as a physical parameter even
though it cancels from the final period ratio.

The amplitude-indexed nonlinear periods are not set equal to harmonic periods.
Instead, their coherent SI readouts converge from positive amplitudes to the
distinguished small-amplitude periods, and only those limits are identified
with the linearized oscillator periods.

None of these fields states the requested ratio or percentage difference.
-/
structure SatisfiesPendulumLaws
    (setup : MeterstickPendulumSetup) : Prop where
  centerOfMassGeometry :
    lengthInMeters setup.centerOfMassDistanceFromPivot =
      lengthInMeters setup.suspensionRodLength +
        lengthInMeters setup.meterstickLength / 2
  uniformMeterstickCenterInertia :
    momentOfInertiaInKilogramMeterSquared
        setup.meterstickInertiaAboutCenter =
      massInKilograms setup.meterstickMass *
        lengthInMeters setup.meterstickLength ^ 2 / 12
  parallelAxisLaw :
    momentOfInertiaInKilogramMeterSquared
        setup.assemblyInertiaAboutPivot =
      momentOfInertiaInKilogramMeterSquared
          setup.meterstickInertiaAboutCenter +
        massInKilograms setup.meterstickMass *
          lengthInMeters setup.centerOfMassDistanceFromPivot ^ 2
  physicalGeneralizedInertia :
    setup.physicalPendulumOscillator.m =
      momentOfInertiaInKilogramMeterSquared
        setup.assemblyInertiaAboutPivot
  physicalNonlinearGravitationalTorque :
    ∀ angleRadians : ℝ,
      torqueInNewtonMeters
          (setup.physicalPendulumGravitationalTorque angleRadians) =
        -(massInKilograms setup.meterstickMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.centerOfMassDistanceFromPivot *
          Real.sin angleRadians)
  physicalGravitationalRestoringCoefficient :
    setup.physicalPendulumOscillator.k =
      massInKilograms setup.meterstickMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        lengthInMeters setup.centerOfMassDistanceFromPivot
  physicalTorqueLinearization :
    HasDerivAt
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
          (setup.physicalPendulumGravitationalTorque angleRadians))
      (-setup.physicalPendulumOscillator.k) 0
  physicalSmallAmplitudePeriodLimit :
    Filter.Tendsto
      (fun amplitudeRadians : ℝ =>
        timeInSeconds
          (setup.physicalPendulumPeriodAtAmplitude amplitudeRadians))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (timeInSeconds setup.physicalPendulumSmallAmplitudePeriod))
  physicalLinearizedLimitPeriod :
    timeInSeconds setup.physicalPendulumSmallAmplitudePeriod =
      setup.physicalPendulumOscillator.period
  referenceGeneralizedInertia :
    setup.referencePendulumOscillator.m =
      massInKilograms setup.referenceBobMass *
        lengthInMeters setup.referencePendulumLength ^ 2
  referenceNonlinearGravitationalTorque :
    ∀ angleRadians : ℝ,
      torqueInNewtonMeters
          (setup.referencePendulumGravitationalTorque angleRadians) =
        -(massInKilograms setup.referenceBobMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters setup.referencePendulumLength *
          Real.sin angleRadians)
  referenceGravitationalRestoringCoefficient :
    setup.referencePendulumOscillator.k =
      massInKilograms setup.referenceBobMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        lengthInMeters setup.referencePendulumLength
  referenceTorqueLinearization :
    HasDerivAt
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
          (setup.referencePendulumGravitationalTorque angleRadians))
      (-setup.referencePendulumOscillator.k) 0
  referenceSmallAmplitudePeriodLimit :
    Filter.Tendsto
      (fun amplitudeRadians : ℝ =>
        timeInSeconds
          (setup.referencePendulumPeriodAtAmplitude amplitudeRadians))
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (timeInSeconds setup.referencePendulumSmallAmplitudePeriod))
  referenceLinearizedLimitPeriod :
    timeInSeconds setup.referencePendulumSmallAmplitudePeriod =
      setup.referencePendulumOscillator.period

/-! ## Percentage readout and answer choices -/

/--
Absolute percentage by which an observed period differs from a positive
reference period.  Both arguments are physical times; only coherent SI
readouts enter the dimensionless ratio.
-/
def periodDifferencePercent
    (observedPeriod referencePeriod : TimeQuantity) : ℝ :=
  100 *
    |timeInSeconds observedPeriod - timeInSeconds referencePeriod| /
      timeInSeconds referencePeriod

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Percentage printed beside each answer label. -/
def AnswerChoice.percent : AnswerChoice → ℝ
  | .A => 208 / 100
  | .B => 308 / 100
  | .C => 508 / 100
  | .D => 408 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A percentage rounds to the same hundredth of a percent as a displayed choice. -/
def RoundsToDisplayedPercentage
    (percentage : ℝ) (choice : AnswerChoice) : Prop :=
  round (100 * percentage) = round (100 * choice.percent)

/-- A displayed choice is at least as close as every listed alternative. -/
def IsClosestDisplayedPercentage
    (percentage : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |percentage - choice.percent| ≤ |percentage - alternative.percent|

/--
In the right-hand zero-amplitude limit, the meterstick assembly has period
ratio `√(13/12)` relative to the `1.00 m` simple pendulum.  Its limiting period
is therefore longer and differs by approximately `4.08%`.  The limiting
percentage rounds to and is closest to recorded answer D.  No exact numerical
claim is made for the unspecified finite release angle.

This formalizes `thm:physics:phyx_mini_0227:target`.
-/
theorem periodDifference_matches_recordedAnswerD
    (setup : MeterstickPendulumSetup)
    (h_figure : MatchesMeterstickPendulumFigure setup)
    (h_data : HasMeterstickPendulumProblemData setup)
    (h_laws : SatisfiesPendulumLaws setup) :
    timeInSeconds setup.physicalPendulumSmallAmplitudePeriod /
          timeInSeconds setup.referencePendulumSmallAmplitudePeriod =
        Real.sqrt ((13 : ℝ) / 12) ∧
      timeInSeconds setup.referencePendulumSmallAmplitudePeriod <
        timeInSeconds setup.physicalPendulumSmallAmplitudePeriod ∧
      RoundsToDisplayedPercentage
        (periodDifferencePercent setup.physicalPendulumSmallAmplitudePeriod
          setup.referencePendulumSmallAmplitudePeriod)
        recordedAnswerChoice ∧
      IsClosestDisplayedPercentage
        (periodDifferencePercent setup.physicalPendulumSmallAmplitudePeriod
          setup.referencePendulumSmallAmplitudePeriod)
        recordedAnswerChoice := by
  rcases h_figure with
    ⟨h_rod_length, h_stick_length, _, _, _, _⟩
  rcases h_data with
    ⟨_, _, _, _, h_reference_length, h_meterstick_mass,
      h_reference_mass, h_gravity⟩
  let M : ℝ := massInKilograms setup.meterstickMass
  let m : ℝ := massInKilograms setup.referenceBobMass
  let g : ℝ :=
    accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  let physical := setup.physicalPendulumOscillator
  let reference := setup.referencePendulumOscillator
  have hM : 0 < M := by
    simpa [M] using h_meterstick_mass
  have hm : 0 < m := by
    simpa [m] using h_reference_mass
  have hg : 0 < g := by
    simpa [g] using h_gravity
  have h_center :
      lengthInMeters setup.centerOfMassDistanceFromPivot = 1 := by
    rw [h_laws.centerOfMassGeometry, h_rod_length, h_stick_length]
    norm_num
  have h_center_inertia :
      momentOfInertiaInKilogramMeterSquared
          setup.meterstickInertiaAboutCenter =
        M / 12 := by
    calc
      momentOfInertiaInKilogramMeterSquared
            setup.meterstickInertiaAboutCenter =
          M * lengthInMeters setup.meterstickLength ^ 2 / 12 := by
            simpa [M] using h_laws.uniformMeterstickCenterInertia
      _ = M / 12 := by rw [h_stick_length]; ring
  have h_pivot_inertia :
      momentOfInertiaInKilogramMeterSquared
          setup.assemblyInertiaAboutPivot =
        13 * M / 12 := by
    calc
      momentOfInertiaInKilogramMeterSquared
            setup.assemblyInertiaAboutPivot =
          momentOfInertiaInKilogramMeterSquared
              setup.meterstickInertiaAboutCenter +
            M * lengthInMeters
                setup.centerOfMassDistanceFromPivot ^ 2 := by
                  simpa [M] using h_laws.parallelAxisLaw
      _ = M / 12 + M * 1 ^ 2 := by rw [h_center_inertia, h_center]
      _ = 13 * M / 12 := by ring
  have h_physical_m : physical.m = 13 * M / 12 := by
    calc
      physical.m =
          momentOfInertiaInKilogramMeterSquared
            setup.assemblyInertiaAboutPivot := by
              simpa [physical] using h_laws.physicalGeneralizedInertia
      _ = 13 * M / 12 := h_pivot_inertia
  have h_physical_k : physical.k = M * g := by
    simpa [physical, M, g, h_center] using
      h_laws.physicalGravitationalRestoringCoefficient
  have h_reference_m : reference.m = m := by
    simpa [reference, m, h_reference_length] using
      h_laws.referenceGeneralizedInertia
  have h_reference_k : reference.k = m * g := by
    simpa [reference, m, g, h_reference_length] using
      h_laws.referenceGravitationalRestoringCoefficient
  have h_physical_omega_sq : physical.ω ^ 2 = 12 * g / 13 := by
    rw [physical.ω_sq, h_physical_k, h_physical_m]
    field_simp [hM.ne']
  have h_reference_omega_sq : reference.ω ^ 2 = g := by
    rw [reference.ω_sq, h_reference_k, h_reference_m]
    field_simp [hm.ne']
  have h_period_ratio_sq :
      (physical.period / reference.period) ^ 2 = (13 : ℝ) / 12 := by
    have h_period_ratio_frequency :
        physical.period / reference.period =
          reference.ω / physical.ω := by
      rw [ClassicalMechanics.HarmonicOscillator.period_eq,
        ClassicalMechanics.HarmonicOscillator.period_eq]
      field_simp [physical.ω_ne_zero, reference.ω_ne_zero,
        Real.pi_ne_zero]
    rw [h_period_ratio_frequency, div_pow, h_reference_omega_sq,
      h_physical_omega_sq]
    field_simp [hg.ne']
  have h_sqrt_sq :
      Real.sqrt ((13 : ℝ) / 12) ^ 2 = (13 : ℝ) / 12 :=
    Real.sq_sqrt (by norm_num)
  have h_period_ratio :
      physical.period / reference.period =
        Real.sqrt ((13 : ℝ) / 12) := by
    have h_ratio_pos : 0 < physical.period / reference.period :=
      div_pos physical.period_pos reference.period_pos
    have h_sqrt_nonneg : 0 ≤ Real.sqrt ((13 : ℝ) / 12) :=
      Real.sqrt_nonneg _
    nlinarith [h_period_ratio_sq, h_sqrt_sq]
  have h_time_ratio :
      timeInSeconds setup.physicalPendulumSmallAmplitudePeriod /
          timeInSeconds setup.referencePendulumSmallAmplitudePeriod =
        Real.sqrt ((13 : ℝ) / 12) := by
    rw [h_laws.physicalLinearizedLimitPeriod,
      h_laws.referenceLinearizedLimitPeriod]
    exact h_period_ratio
  have h_reference_period_pos :
      0 < timeInSeconds setup.referencePendulumSmallAmplitudePeriod := by
    rw [h_laws.referenceLinearizedLimitPeriod]
    exact reference.period_pos
  have h_physical_period_pos :
      0 < timeInSeconds setup.physicalPendulumSmallAmplitudePeriod := by
    rw [h_laws.physicalLinearizedLimitPeriod]
    exact physical.period_pos
  have h_sqrt_gt_one : 1 < Real.sqrt ((13 : ℝ) / 12) := by
    nlinarith [h_sqrt_sq, Real.sqrt_nonneg ((13 : ℝ) / 12)]
  have h_physical_period_eq :
      timeInSeconds setup.physicalPendulumSmallAmplitudePeriod =
        Real.sqrt ((13 : ℝ) / 12) *
          timeInSeconds setup.referencePendulumSmallAmplitudePeriod :=
    (div_eq_iff h_reference_period_pos.ne').mp h_time_ratio
  have h_period_lt :
      timeInSeconds setup.referencePendulumSmallAmplitudePeriod <
        timeInSeconds setup.physicalPendulumSmallAmplitudePeriod := by
    calc
      timeInSeconds setup.referencePendulumSmallAmplitudePeriod =
          1 * timeInSeconds
            setup.referencePendulumSmallAmplitudePeriod := by ring
      _ < Real.sqrt ((13 : ℝ) / 12) *
          timeInSeconds setup.referencePendulumSmallAmplitudePeriod :=
            mul_lt_mul_of_pos_right h_sqrt_gt_one h_reference_period_pos
      _ = timeInSeconds
          setup.physicalPendulumSmallAmplitudePeriod :=
            h_physical_period_eq.symm
  have h_percentage :
      periodDifferencePercent setup.physicalPendulumSmallAmplitudePeriod
          setup.referencePendulumSmallAmplitudePeriod =
        100 * (Real.sqrt ((13 : ℝ) / 12) - 1) := by
    rw [periodDifferencePercent, abs_of_pos (sub_pos.mpr h_period_lt),
      h_physical_period_eq]
    field_simp [h_reference_period_pos.ne']
  have h_sqrt_lower :
      (1301 : ℝ) / 1250 < Real.sqrt ((13 : ℝ) / 12) := by
    by_contra h
    push Not at h
    nlinarith [h_sqrt_sq, Real.sqrt_nonneg ((13 : ℝ) / 12)]
  have h_sqrt_upper :
      Real.sqrt ((13 : ℝ) / 12) < (20817 : ℝ) / 20000 := by
    by_contra h
    push Not at h
    nlinarith [h_sqrt_sq, Real.sqrt_nonneg ((13 : ℝ) / 12)]
  have h_percentage_lower :
      (408 : ℝ) / 100 <
        periodDifferencePercent setup.physicalPendulumSmallAmplitudePeriod
          setup.referencePendulumSmallAmplitudePeriod := by
    rw [h_percentage]
    linarith
  have h_percentage_upper :
      periodDifferencePercent setup.physicalPendulumSmallAmplitudePeriod
          setup.referencePendulumSmallAmplitudePeriod <
        (817 : ℝ) / 200 := by
    rw [h_percentage]
    linarith
  refine ⟨h_time_ratio, h_period_lt, ?_, ?_⟩
  · unfold RoundsToDisplayedPercentage
    have h_round_observed :
        round
            (100 *
              periodDifferencePercent
                setup.physicalPendulumSmallAmplitudePeriod
                setup.referencePendulumSmallAmplitudePeriod) =
          (408 : ℤ) := by
      rw [round_eq_iff]
      change
        (408 : ℝ) - 1 / 2 ≤
            100 *
              periodDifferencePercent
                setup.physicalPendulumSmallAmplitudePeriod
                setup.referencePendulumSmallAmplitudePeriod ∧
          100 *
              periodDifferencePercent
                setup.physicalPendulumSmallAmplitudePeriod
                setup.referencePendulumSmallAmplitudePeriod <
            (408 : ℝ) + 1 / 2
      constructor
      · nlinarith only [h_percentage_lower]
      · nlinarith only [h_percentage_upper]
    rw [h_round_observed]
    norm_num [recordedAnswerChoice, AnswerChoice.percent, round_eq_iff]
  · unfold IsClosestDisplayedPercentage
    intro alternative
    cases alternative <;>
      simp only [recordedAnswerChoice, AnswerChoice.percent]
    · rw [abs_of_nonneg (by linarith only [h_percentage_lower]),
        abs_of_nonneg (by linarith only [h_percentage_lower])]
      linarith only
    · rw [abs_of_nonneg (by linarith only [h_percentage_lower]),
        abs_of_nonneg (by linarith only [h_percentage_lower])]
      linarith only
    · rw [abs_of_nonneg (by linarith only [h_percentage_lower]),
        abs_of_nonpos (by linarith only [h_percentage_upper])]
      linarith only [h_percentage_upper]
    · exact le_rfl

end PhyXMiniProblems.ProblemPhyXMini0227
