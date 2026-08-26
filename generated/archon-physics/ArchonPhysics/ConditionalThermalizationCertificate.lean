import ArchonPhysics.ENNRealWindowConvergence
import ArchonPhysics.MeasurableHittingTime

/-!
# Conditional microscopic-to-thermalization certificate

This module is the minimal composition layer between model-specific microscopic
estimates and the already verified probabilistic hitting-time transfer.  The
certificate below contains no scaling-window law and no
`G2TeqConvergesInProbability` conclusion.  Its local-error estimate and the
identification of the model's scaled equilibration time with a threshold
hitting time are the remaining hypotheses that a concrete microscopic theory
must discharge.
-/

namespace ArchonPhysics

open Filter MeasureTheory Set Topology
open ThermalizationTransfer
open ENNRealWindowConvergence
open MeasurableHittingTime

noncomputable section

/--
The unresolved, model-specific inputs needed to transfer a kinetic robust
crossing to microscopic thermalization along every admissible joint limit.

The distance path and error gauge are explicit finite-model data.  Only their
behavior along admitted joint limits is required.  In particular, this
structure does not assume the desired hitting-time limit, a scaling-window
probability law, or either final thermalization structure.
-/
structure ConditionalThermalizationCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta : Real) where
  /-- The rescaled microscopic distance path for finite size and coupling. -/
  scaledMicroscopicDistance :
    Nat → Real → Omega → Real → Real
  /-- A finite-model gauge controlling local-uniform kinetic approximation. -/
  localUniformError :
    Real → Nat → Real → Omega → ENNReal
  /-- Measurability of the error gauge along every admitted joint limit. -/
  localUniformError_measurable :
    ∀ s : AdmissibleJointLimit sizeCutoff, ∀ T j,
      Measurable (localUniformError T (s.systemSize j) (s.coupling j))
  /--
  Remaining microscopic estimate: the error gauge tends to zero in probability
  on every positive compact time window along each admitted joint limit.
  -/
  localUniformError_zero_law :
    ∀ s : AdmissibleJointLimit sizeCutoff, ∀ T, 0 < T →
      ∀ U : Set ENNReal, MeasurableSet U → U ∈ 𝓝 0 →
        Tendsto
          (fun j => P
            ((localUniformError T (s.systemSize j) (s.coupling j)) ⁻¹' U))
          atTop (𝓝 1)
  /-- The error gauge genuinely controls the displayed microscopic path. -/
  localUniformError_controls :
    ∀ s : AdmissibleJointLimit sizeCutoff,
      ∀ T eta, 0 < T → 0 < eta → ∀ j omega,
        localUniformError T (s.systemSize j) (s.coupling j) omega <
            ENNReal.ofReal eta →
          UniformlyCloseOnNonnegativeWindow
            (scaledMicroscopicDistance
              (s.systemSize j) (s.coupling j) omega)
            kineticDistance T eta
  /-- Measurability of the microscopic path at every rational test time. -/
  scaledMicroscopicDistance_rat_measurable :
    ∀ s : AdmissibleJointLimit sizeCutoff, ∀ j, ∀ q : Rat,
      Measurable (fun omega => scaledMicroscopicDistance
        (s.systemSize j) (s.coupling j) omega (q : Real))
  /-- Remaining entry condition grounding closed-threshold hitting measurability. -/
  closedThreshold_rationalStrictEntry :
    ∀ s : AdmissibleJointLimit sizeCutoff, ∀ j omega,
      RationalStrictEntryCondition (scaledMicroscopicDistance
        (s.systemSize j) (s.coupling j) omega) delta
  /-- The original finite-model equilibration time is measurable. -/
  equilibrationTime_measurable :
    ∀ N g, Measurable (equilibrationTime N g)
  /--
  Remaining model identification: the physical scaled equilibration time is
  exactly the threshold hitting time of the displayed scaled distance path.
  -/
  scaledEquilibrationTime_eq_hittingTime :
    ∀ s : AdmissibleJointLimit sizeCutoff, ∀ j omega,
      scaledEquilibrationTime equilibrationTime
          (s.systemSize j) (s.coupling j) omega =
        distanceThresholdHittingTime
          (scaledMicroscopicDistance
            (s.systemSize j) (s.coupling j) omega) delta

/-- The two explicit error-gauge fields assemble the existing probability-zero interface. -/
theorem ConditionalThermalizationCertificate.localUniformError_convergesInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta : Real)
    (certificate : ConditionalThermalizationCertificate P equilibrationTime
      sizeCutoff kineticDistance delta)
    (s : AdmissibleJointLimit sizeCutoff) (T : Real) (hT : 0 < T) :
    ConvergesInProbabilityTo P
      (fun j omega => certificate.localUniformError T
        (s.systemSize j) (s.coupling j) omega) 0 := by
  constructor
  · intro j
    exact certificate.localUniformError_measurable s T j
  · exact certificate.localUniformError_zero_law s T hT

/--
A robust kinetic crossing plus the transparent microscopic certificate really
constructs the enhanced `g² T_eq` convergence law.  No probability window or
thermalization conclusion occurs among the hypotheses.
-/
theorem ConditionalThermalizationCertificate.toG2TeqConvergesInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tauStar : Real)
    (certificate : ConditionalThermalizationCertificate P equilibrationTime
      sizeCutoff kineticDistance delta)
    (hcross : RobustKineticFirstCrossing kineticDistance delta tauStar) :
    G2TeqConvergesInProbability P equilibrationTime
      sizeCutoff tauStar := by
  refine ⟨hcross.tauStar_pos, certificate.equilibrationTime_measurable, ?_⟩
  intro s
  have hhitting :
      ConvergesInProbabilityTo P
        (fun j omega => distanceThresholdHittingTime
          (certificate.scaledMicroscopicDistance
            (s.systemSize j) (s.coupling j) omega) delta)
        (ENNReal.ofReal tauStar) := by
    exact random_local_uniform_error_implies_hitting_time_convergence
      P
      (fun j omega => certificate.scaledMicroscopicDistance
        (s.systemSize j) (s.coupling j) omega)
      (fun T j omega => certificate.localUniformError T
        (s.systemSize j) (s.coupling j) omega)
      delta tauStar hcross
      (fun T hT =>
        certificate.localUniformError_convergesInProbability
          P equilibrationTime sizeCutoff kineticDistance delta s T hT)
      (fun T eta hT heta j omega hsmall =>
        certificate.localUniformError_controls
          s T eta hT heta j omega hsmall)
      (fun j =>
        measurable_distanceThresholdHittingTime_of_rationalStrictEntry
          (fun omega => certificate.scaledMicroscopicDistance
            (s.systemSize j) (s.coupling j) omega)
          delta
          (certificate.scaledMicroscopicDistance_rat_measurable s j)
          (certificate.closedThreshold_rationalStrictEntry s j))
  have hidentification :
      (fun j omega => scaledEquilibrationTime equilibrationTime
        (s.systemSize j) (s.coupling j) omega) =
      (fun j omega => distanceThresholdHittingTime
        (certificate.scaledMicroscopicDistance
          (s.systemSize j) (s.coupling j) omega) delta) := by
    funext j omega
    exact certificate.scaledEquilibrationTime_eq_hittingTime s j omega
  rw [hidentification]
  exact hhitting

/-- Every strictly bracketing positive kinetic window follows as a corollary. -/
theorem ConditionalThermalizationCertificate.toHighProbabilityG2Bounds
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tauStar lower upper : Real)
    (certificate : ConditionalThermalizationCertificate P equilibrationTime
      sizeCutoff kineticDistance delta)
    (hcross : RobustKineticFirstCrossing kineticDistance delta tauStar)
    (hlower_pos : 0 < lower) (hlower : lower < tauStar)
    (hupper : tauStar < upper) :
    HighProbabilityG2Bounds P equilibrationTime sizeCutoff lower upper := by
  exact G2TeqConvergesInProbability.toHighProbabilityG2Bounds
    P equilibrationTime sizeCutoff tauStar lower upper
    (certificate.toG2TeqConvergesInProbability
      P equilibrationTime sizeCutoff kineticDistance delta tauStar hcross)
    hlower_pos hlower hupper

end

end ArchonPhysics
