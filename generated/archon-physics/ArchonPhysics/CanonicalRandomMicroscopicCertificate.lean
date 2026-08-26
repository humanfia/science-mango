import ArchonPhysics.CanonicalRandomMassPhasePositiveDenominator
import ArchonPhysics.OrderedTranslationLastMode

/-!
# Canonical random microscopic F1 certificate

This module only packages already proved microscopic facts.  In particular,
the `ENNReal` hitting times below are allowed to equal `⊤`; no finiteness,
kinetic approximation, or inverse-square scaling statement is included.
-/

namespace ArchonPhysics.CanonicalRandomMicroscopicCertificate

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CanonicalRandomMassPhasePositiveDenominator
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.RandomMassReducedPhaseInitialData
open MeasureTheory
open ProbabilityTheory

noncomputable section

/-- The canonical positive-rational strict-threshold equilibration time.
It is an `ENNReal` random variable and may be `⊤`. -/
def equilibrationTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu delta : Real) : RandomEnsemble.SampleSpace → ENNReal :=
  canonicalFrozenRationalStrictHittingTime
    (N := N) kappa beta g hbeta a mu delta

/-- The canonical fixed-duration rational-persistence equilibration time.
It too may be `⊤`. -/
def persistentEquilibrationTime
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu delta duration : Real) :
    RandomEnsemble.SampleSpace → ENNReal :=
  canonicalFrozenRationalPersistentHittingTime
    (N := N) kappa beta g hbeta a mu delta duration

/-- If no positive rational candidate enters the strict threshold, the total
`ENNReal` convention assigns the equilibration time the value `⊤`. -/
theorem equilibrationTime_eq_top_of_no_candidate
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu delta : Real) (omega : RandomEnsemble.SampleSpace)
    (hno : ∀ q : Rat,
      ¬ (0 < ENNReal.ofReal (q : Real) ∧
        canonicalFrozenLateWindowL1Distance
          (N := N) kappa beta g hbeta a mu (q : Real) omega < delta)) :
    equilibrationTime (N := N)
      kappa beta g hbeta a mu delta omega = ⊤ := by
  unfold equilibrationTime canonicalFrozenRationalStrictHittingTime
    sampledPositiveLateWindowRationalStrictHittingTime
    MeasurableHittingTime.rationalStrictDistanceThresholdHittingTime
  apply top_unique
  apply le_iInf
  intro q
  rw [if_neg]
  simpa only [canonicalFrozenLateWindowL1Distance] using hno q

/-- The almost-sure physical content of the canonical ambient random orbit.
The witness is a genuine untruncated reduced Hamiltonian trajectory. -/
def PhysicalRealization
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : RandomEnsemble.SampleSpace) : Prop :=
  ∃ hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)),
    ∃ z : Real → ReducedPhaseSpace
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega),
      z 0 = reducedInitialStateOfSimple
        canonicalIIDMassPhaseEnsemble a omega hsimple ∧
      (∀ t, HasDerivAt z
        (reducedVectorField
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t)) t) ∧
      (∀ t, canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta
          (canonicalPhaseInitialSample (N := N) kappa beta g a omega, t) =
        embedReducedPoint
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) kappa beta g (z t)) ∧
      ∀ t k, sampledPhysicalOrderedModeEnergyAlongFlow
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
          (canonicalPhaseInitialSample (N := N) kappa beta g a)
          (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
          (omega, t) k =
        reducedPhysicalOrderedModeEnergy
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega) (z t) k

/-- The canonical initial state realizes the frozen full ordered energy
profile, including zero energy in the translation mode and total energy one. -/
def InitialProfileIsExact
    {N : Nat} [NeZero N] (a : Real)
    (omega : RandomEnsemble.SampleSpace) : Prop :=
  (∀ k : OrderedModeIndex N,
    RandomMassMeasurableHarmonicEnergy.harmonicOrderedPhysicalModeEnergy
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (initialPhysicalPosition canonicalIIDMassPhaseEnsemble a)
        (initialPhysicalMomentum canonicalIIDMassPhaseEnsemble a) omega k =
      orderedTargetEnergy N a k) ∧
  (∑ k : OrderedModeIndex N,
    RandomMassMeasurableHarmonicEnergy.harmonicOrderedPhysicalModeEnergy
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
        (initialPhysicalPosition canonicalIIDMassPhaseEnsemble a)
        (initialPhysicalMomentum canonicalIIDMassPhaseEnsemble a) omega k) = 1

theorem initialProfileIsExact_ae
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      InitialProfileIsExact (N := N) a omega := by
  simpa only [InitialProfileIsExact] using
    canonicalPhaseInitial_exact_profile_ae hN ha0 ha1

/-- Almost surely the positive-frequency mask contains exactly all `N - 1`
nontranslation modes. -/
theorem positiveModeCount_ae
    {N : Nat} [NeZero N] (hN : 3 ≤ N) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      (positiveModeIndices
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega))).card = N - 1 := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega)
  filter_upwards [hsimpleAE] with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian] using hsimpleSample
  rw [positiveModeIndices_eq_univ_erase_last _ hsimple]
  simp

/-- Almost surely the canonical jointly measurable orbit is a genuine
untruncated reduced Hamiltonian orbit, mode by mode and for every real time. -/
theorem physicalRealization_ae
    {N : Nat} [NeZero N]
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      PhysicalRealization (N := N) kappa beta g hbeta a omega := by
  have hphysical :=
    canonicalFrozenLateWindowL1Distance_matches_reduced_ae
      hN ha0 ha1 kappa beta g hbeta 0 0
  filter_upwards [hphysical] with omega homega
  rcases homega with
    ⟨hsimple, z, hz0, hz, hmatch, hmode, _hdistance⟩
  exact ⟨hsimple, z, hz0, hz, hmatch, hmode⟩

/-- Every physical-realization witness identifies the complete normalized
late-window distance with the same diagnostic on its reduced trajectory. -/
theorem PhysicalRealization.exists_lateWindow_eq_reduced
    {N : Nat} [NeZero N]
    {kappa beta g : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {a : Real} {omega : RandomEnsemble.SampleSpace}
    (hphysical : PhysicalRealization (N := N)
      kappa beta g hbeta a omega) (mu T : Real) :
    ∃ _hsimple : SimpleOrderedSpectrum
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega)),
      ∃ z : Real → ReducedPhaseSpace
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega),
        canonicalFrozenLateWindowL1Distance
            (N := N) kappa beta g hbeta a mu T omega =
          reducedTrajectoryPositiveLateWindowL1Distance
            (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
              (N := N) omega) z mu T := by
  rcases hphysical with ⟨hsimple, z, _hz0, _hz, hmatch, _hmode⟩
  refine ⟨hsimple, z, ?_⟩
  exact sampledPositiveLateWindowL1Distance_eq_reduced_of_match
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a)
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
    kappa beta g omega z hmatch mu T

/-- One transparent certificate for the kernel-closed F1 random microscopic
construction.  No field asserts that either hitting time is finite. -/
structure Certificate
    (N : Nat) [NeZero N] (kappa beta g a : Real) : Prop where
  size_at_least_three : 3 ≤ N
  profile_nonnegative : 0 ≤ a
  profile_le_quarter : a ≤ 1 / 4
  coercive : 2 * kappa ^ 2 / 9 < beta
  mass_coordinate_law : ∀ n,
    HasLaw (canonicalIIDMassPhaseEnsemble.mass n)
      RandomEnsemble.massCoordinateLaw
      canonicalIIDMassPhaseEnsemble.probability
  phase_coordinate_law : ∀ n,
    HasLaw (canonicalIIDMassPhaseEnsemble.phase n)
      RandomEnsemble.phaseCoordinateLaw
      canonicalIIDMassPhaseEnsemble.probability
  mass_coordinates_independent :
    iIndepFun canonicalIIDMassPhaseEnsemble.mass
      canonicalIIDMassPhaseEnsemble.probability
  phase_coordinates_independent :
    iIndepFun canonicalIIDMassPhaseEnsemble.phase
      canonicalIIDMassPhaseEnsemble.probability
  mass_phase_blocks_independent :
    IndepFun
      (fun omega n ↦ canonicalIIDMassPhaseEnsemble.mass n omega)
      (fun omega n ↦ canonicalIIDMassPhaseEnsemble.phase n omega)
      canonicalIIDMassPhaseEnsemble.probability
  finite_mass_measurable : Measurable
    (canonicalIIDMassPhaseEnsemble.restrictMass (N := N))
  finite_phase_measurable : Measurable
    (canonicalIIDMassPhaseEnsemble.restrictPhase (N := N))
  finite_mass_phase_independent : IndepFun
    (canonicalIIDMassPhaseEnsemble.restrictMass (N := N))
    (canonicalIIDMassPhaseEnsemble.restrictPhase (N := N))
    canonicalIIDMassPhaseEnsemble.probability
  initial_sample_measurable : Measurable
    (canonicalPhaseInitialSample (N := N) kappa beta g a)
  common_global_flow_measurable : Measurable
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g coercive)
  random_trajectory_measurable : Measurable
    (canonicalRandomMassPhaseTrajectory (N := N)
      canonicalIIDMassPhaseEnsemble kappa beta g coercive a)
  random_trajectory_continuous : ∀ omega, Continuous (fun t =>
    canonicalRandomMassPhaseTrajectory (N := N)
      canonicalIIDMassPhaseEnsemble kappa beta g coercive a (omega, t))
  initial_profile_exact_ae :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      InitialProfileIsExact (N := N) a omega
  positive_mode_count_ae :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      (positiveModeIndices
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := N) omega))).card = N - 1
  normalized_lateWindow_measurable : ∀ mu T, Measurable
    (sampledPositiveLateWindowNormalizedWeights
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g a)
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g coercive) mu T)
  positive_lateWindow_total_ae : ∀ mu T, 0 ≤ mu → mu < 1 → 0 < T →
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      0 < canonicalFrozenPositiveLateWindowTotalWeight
        (N := N) kappa beta g coercive a mu T omega
  normalized_lateWindow_sum_one_ae :
    ∀ mu T, 0 ≤ mu → mu < 1 → 0 < T →
      ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
        (∑ k : OrderedModeIndex N,
          canonicalFrozenPositiveLateWindowNormalizedWeights
            (N := N) kappa beta g coercive a mu T omega k) = 1
  lateWindow_distance_measurable : ∀ mu T, Measurable
    (canonicalFrozenLateWindowL1Distance
      (N := N) kappa beta g coercive a mu T)
  equilibration_time_measurable : ∀ mu delta, Measurable
    (equilibrationTime (N := N) kappa beta g coercive a mu delta)
  persistent_equilibration_time_measurable : ∀ mu delta duration, Measurable
    (persistentEquilibrationTime (N := N)
      kappa beta g coercive a mu delta duration)
  physical_realization_ae :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      PhysicalRealization (N := N) kappa beta g coercive a omega

/-- The canonical iid mass/Haar-phase construction supplies every field of
the F1 certificate without a model-specific assumption. -/
theorem exists_certificate
    {N : Nat} [NeZero N]
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    Certificate N kappa beta g a := by
  refine
    { size_at_least_three := hN
      profile_nonnegative := ha0
      profile_le_quarter := ha1
      coercive := hbeta
      mass_coordinate_law := canonicalIIDMassPhaseEnsemble.mass_hasLaw
      phase_coordinate_law := canonicalIIDMassPhaseEnsemble.phase_hasLaw
      mass_coordinates_independent := canonicalIIDMassPhaseEnsemble.mass_iIndep
      phase_coordinates_independent := canonicalIIDMassPhaseEnsemble.phase_iIndep
      mass_phase_blocks_independent :=
        canonicalIIDMassPhaseEnsemble.mass_phase_indep
      finite_mass_measurable :=
        canonicalIIDMassPhaseEnsemble.measurable_restrictMass
      finite_phase_measurable :=
        canonicalIIDMassPhaseEnsemble.measurable_restrictPhase
      finite_mass_phase_independent :=
        canonicalIIDMassPhaseEnsemble.restrictMass_indep_restrictPhase
      initial_sample_measurable :=
        measurable_canonicalPhaseInitialSample kappa beta g a
      common_global_flow_measurable :=
        measurable_canonicalRandomMassPhaseGlobalFlow kappa beta g hbeta
      random_trajectory_measurable :=
        measurable_canonicalRandomMassPhaseTrajectory
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
      random_trajectory_continuous :=
        continuous_canonicalRandomMassPhaseTrajectory_path
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
      initial_profile_exact_ae := initialProfileIsExact_ae hN ha0 ha1
      positive_mode_count_ae := positiveModeCount_ae hN
      normalized_lateWindow_measurable := ?_
      positive_lateWindow_total_ae :=
        canonicalFrozenPositiveLateWindowTotalWeight_pos_ae
          hN ha0 ha1 kappa beta g hbeta
      normalized_lateWindow_sum_one_ae :=
        sum_canonicalFrozenPositiveLateWindowNormalizedWeights_ae
          hN ha0 ha1 kappa beta g hbeta
      lateWindow_distance_measurable := ?_
      equilibration_time_measurable := ?_
      persistent_equilibration_time_measurable := ?_
      physical_realization_ae :=
        physicalRealization_ae hN ha0 ha1 kappa beta g hbeta }
  · intro mu T
    exact measurable_sampledPositiveLateWindowNormalizedWeights
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g a)
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
      (RandomMassOrderedProjectorBridge.measurable_restrictPositiveMass_coordinate
        canonicalIIDMassPhaseEnsemble)
      (measurable_canonicalPhaseInitialSample kappa beta g a)
      (measurable_canonicalRandomMassPhaseGlobalFlow kappa beta g hbeta)
      mu T
  · intro mu T
    exact measurable_canonicalFrozenLateWindowL1Distance
      kappa beta g hbeta a mu T
  · intro mu delta
    simpa only [equilibrationTime] using
      measurable_canonicalFrozenRationalStrictHittingTime
        (N := N) kappa beta g hbeta a mu delta
  · intro mu delta duration
    simpa only [persistentEquilibrationTime] using
      measurable_canonicalFrozenRationalPersistentHittingTime
        (N := N) kappa beta g hbeta a mu delta duration

/-- Frozen v0.3 specialization at the macroscopic two-band amplitude `1 / 4`.
The underlying target profile is uniformly separated from positive-mode
equipartition by `1 / 8`. -/
theorem exists_frozenQuarter_certificate
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    Certificate N kappa beta g (1 / 4) :=
  exists_certificate hN (by norm_num) (by norm_num)
    kappa beta g hbeta

end

end ArchonPhysics.CanonicalRandomMicroscopicCertificate
