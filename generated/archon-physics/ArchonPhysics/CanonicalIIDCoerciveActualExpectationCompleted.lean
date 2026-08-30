import ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem

/-!
# Completed actual canonical iid expectation hierarchy

The pointwise constants proved in the preceding adapter files are lifted here
to one full-measure, all-time set, arbitrary fixed finite signed blocks, and
their exact one-slot alpha--beta source insertions.  This proves Bochner
integrability and closes differentiation under the canonical iid expectation
without abstract domination or base-integrability premises.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open MeasureTheory
open Metric

noncomputable section

variable {N : Nat} [NeZero N]

theorem canonicalSignedAmplitudeEnvelope_nonneg
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    0 ≤ canonicalSignedAmplitudeEnvelope N kappa beta g hbeta := by
  unfold canonicalSignedAmplitudeEnvelope
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (Real.sqrt_nonneg 5)
        (canonicalWeightedCoordinateEnvelope_nonneg kappa beta g hbeta))
      (canonicalWeightedCoordinateEnvelope_nonneg kappa beta g hbeta))
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg

theorem canonicalSignedSourceEnvelope_nonneg
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    0 ≤ canonicalSignedSourceEnvelope N kappa beta g hbeta := by
  unfold canonicalSignedSourceEnvelope
  exact mul_nonneg
    (canonicalTransformedNonlinearForceEnvelope_nonneg kappa beta g _
      (canonicalWeightedCoordinateEnvelope_nonneg kappa beta g hbeta))
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg

theorem norm_canonicalInteractionAmplitude_le_envelope_of_simple
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N)
    (hk : k ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real)
    (hq : ‖canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius)
    (hp : ‖canonicalFlowMomentum (N := N)
        kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius) :
    ‖canonicalInteractionAmplitude (N := N)
        kappa beta g hbeta a k (omega, time)‖ ≤
      canonicalSignedAmplitudeEnvelope N kappa beta g hbeta := by
  let B := canonicalWeightedCoordinateEnvelope N kappa beta g hbeta
  have hwpos := canonicalOrderedFrequency_pos k hk omega
  have hwupper := canonicalOrderedFrequency_le_sqrt_five k omega
  have hQ := abs_canonicalOrderedModalPosition_le_envelope_of_simple
    kappa beta g hbeta a omega hsimple k time hq
  have hP := abs_canonicalOrderedModalMomentum_le_envelope_of_simple
    kappa beta g hbeta a omega hsimple k time hp
  have hnorm := norm_complexModeAmplitude_le hwpos hwupper
    (Real.sqrt_nonneg 5) hQ hP
    (canonicalWeightedCoordinateEnvelope_nonneg kappa beta g hbeta)
    (inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope k hk omega)
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg
  rw [canonicalInteractionAmplitude, norm_phaseRenormalize]
  simpa [canonicalSignedAmplitudeEnvelope, B] using hnorm

theorem norm_canonicalSignedInteractionAmplitude_le_envelope_of_simple
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real)
    (hq : ‖canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius)
    (hp : ‖canonicalFlowMomentum (N := N)
        kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius) :
    ‖canonicalSignedInteractionAmplitude (N := N)
        kappa beta g hbeta a entry (omega, time)‖ ≤
      canonicalSignedAmplitudeEnvelope N kappa beta g hbeta := by
  rw [canonicalSignedInteractionAmplitude,
    norm_phaseSignActComplex]
  exact norm_canonicalInteractionAmplitude_le_envelope_of_simple
    kappa beta g hbeta a omega hsimple entry.2 hentry time hq hp

theorem norm_canonicalOrderedRotatedSource_le_envelope_of_simple
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N)
    (hk : k ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real)
    (hq : ‖canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius) :
    ‖canonicalOrderedRotatedSource (N := N)
        kappa beta g hbeta a k (omega, time)‖ ≤
      canonicalSignedSourceEnvelope N kappa beta g hbeta := by
  let B := canonicalWeightedCoordinateEnvelope N kappa beta g hbeta
  let q := canonicalFlowPosition (N := N)
    kappa beta g hbeta a (omega, time)
  have hB0 : 0 ≤ B :=
    canonicalWeightedCoordinateEnvelope_nonneg kappa beta g hbeta
  have hbond : ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| ≤ B := by
    intro i
    calc
      |Lattice.forwardDifference (asConfiguration q) i| ≤ 2 * ‖q‖ :=
        abs_forwardDifference_le_two_mul_norm q i
      _ ≤ 2 * canonicalNonnegativeShellRadius N kappa beta g hbeta := by
        gcongr
        exact hq.trans (le_max_left _ _)
      _ = B := rfl
  have hforceNorm :
      ‖transformedNonlinearForce (canonicalMass (N := N) omega)
          kappa beta g q‖ ≤
        canonicalTransformedNonlinearForceEnvelope N kappa beta g B :=
    norm_transformedNonlinearForce_le_envelope
      (canonicalMass (N := N) omega) (canonicalMass_lower omega)
      kappa beta g B hB0 q hbond
  have hproject :
      |orderedSignedNonlinearForce (canonicalMass (N := N) omega)
          kappa beta g k q| ≤
        canonicalTransformedNonlinearForceEnvelope N kappa beta g B :=
    (abs_orderedSignedCoordinate_le_norm
      (canonicalMass (N := N) omega) hsimple k
      (transformedNonlinearForce (canonicalMass (N := N) omega)
        kappa beta g q)).trans hforceNorm
  have hsource := norm_forcedModeSource_le
    (canonicalOrderedFrequency_pos k hk omega)
    (inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope k hk omega)
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg
    (force := orderedSignedNonlinearForce
      (canonicalMass (N := N) omega) kappa beta g k q)
  calc
    ‖canonicalOrderedRotatedSource (N := N)
        kappa beta g hbeta a k (omega, time)‖ =
        ‖forcedModeSource (canonicalOrderedFrequency (N := N) k omega)
          (orderedSignedNonlinearForce (canonicalMass (N := N) omega)
            kappa beta g k q)‖ := by
      simp [canonicalOrderedRotatedSource, orderedSignedRotatedSource,
        canonicalOrderedFrequency, q]
    _ ≤ |orderedSignedNonlinearForce (canonicalMass (N := N) omega)
          kappa beta g k q| *
        canonicalPositiveFrequencyNormalizationEnvelope N := hsource
    _ ≤ canonicalTransformedNonlinearForceEnvelope N kappa beta g B *
        canonicalPositiveFrequencyNormalizationEnvelope N := by
      exact mul_le_mul_of_nonneg_right hproject
        canonicalPositiveFrequencyNormalizationEnvelope_nonneg
    _ = canonicalSignedSourceEnvelope N kappa beta g hbeta := by
      simp [canonicalSignedSourceEnvelope, B]

theorem norm_canonicalSignedRotatedSource_le_envelope_of_simple
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (time : Real)
    (hq : ‖canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius) :
    ‖canonicalSignedRotatedSource (N := N)
        kappa beta g hbeta a entry (omega, time)‖ ≤
      canonicalSignedSourceEnvelope N kappa beta g hbeta := by
  rw [canonicalSignedRotatedSource, norm_phaseSignActComplex]
  exact norm_canonicalOrderedRotatedSource_le_envelope_of_simple
    kappa beta g hbeta a omega hsimple entry.2 hentry time hq

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem norm_finite_signed_block_le
    (amplitude : I → Complex) (block : Finset I) {A : Real}
    (hA : 0 ≤ A) (hamp : ∀ i ∈ block, ‖amplitude i‖ ≤ A) :
    ‖∏ i ∈ block, amplitude i‖ ≤ canonicalSignedBlockEnvelope A block := by
  let L := 1 + A
  have hL : 0 ≤ L := by dsimp [L]; linarith
  calc
    ‖∏ i ∈ block, amplitude i‖ = ∏ i ∈ block, ‖amplitude i‖ := by
      simpa using Complex.norm_prod block amplitude
    _ ≤ ∏ _i ∈ block, L := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg (amplitude i)
      · intro i hi
        dsimp [L]
        linarith [hamp i hi]
    _ = canonicalSignedBlockEnvelope A block := by
      simp [canonicalSignedBlockEnvelope, L]

theorem norm_finite_signed_insertion_le
    (amplitude source : I → Complex) (block : Finset I) {A S : Real}
    (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hamp : ∀ i ∈ block, ‖amplitude i‖ ≤ A)
    (hsource : ∀ i ∈ block, ‖source i‖ ≤ S) :
    ‖∑ i ∈ block,
        (∏ j ∈ block.erase i, amplitude j) * source i‖ ≤
      canonicalSignedBlockInsertionEnvelope A S block := by
  let L := 1 + A
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := le_trans (by norm_num) hLone
  have hproduct (i : I) (hi : i ∈ block) :
      ‖∏ j ∈ block.erase i, amplitude j‖ ≤
        canonicalSignedBlockEnvelope A block := by
    calc
      ‖∏ j ∈ block.erase i, amplitude j‖ ≤
          canonicalSignedBlockEnvelope A (block.erase i) := by
        apply norm_finite_signed_block_le amplitude (block.erase i) hA
        intro j hj
        exact hamp j (Finset.mem_of_mem_erase hj)
      _ ≤ canonicalSignedBlockEnvelope A block := by
        unfold canonicalSignedBlockEnvelope
        exact pow_le_pow_right₀ hLone
          (Finset.card_le_card (Finset.erase_subset i block))
  calc
    ‖∑ i ∈ block,
        (∏ j ∈ block.erase i, amplitude j) * source i‖ ≤
        ∑ i ∈ block,
          ‖(∏ j ∈ block.erase i, amplitude j) * source i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ block,
        canonicalSignedBlockEnvelope A block * S := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul (hproduct i hi) (hsource i hi)
        (norm_nonneg _) (by
          unfold canonicalSignedBlockEnvelope
          positivity)
    _ = canonicalSignedBlockInsertionEnvelope A S block := by
      simp [canonicalSignedBlockInsertionEnvelope]
      ring

theorem canonicalSignedBlockBounds_ae_allTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N)) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ time : Real, ∀ block : Finset I,
        ‖canonicalSignedBlockObservable (N := N)
            kappa beta g hbeta a entry block (omega, time)‖ ≤
          canonicalSignedBlockEnvelope
            (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta) block ∧
        ‖canonicalSignedBlockInsertion (N := N)
            kappa beta g hbeta a entry block (omega, time)‖ ≤
          canonicalSignedBlockInsertionEnvelope
            (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
            (canonicalSignedSourceEnvelope N kappa beta g hbeta) block := by
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega),
    norm_canonicalFlowPosition_le_cutoffRadius_ae_allTime
      hN ha0 ha1 kappa beta g hbeta,
    norm_canonicalFlowMomentum_le_cutoffRadius_ae_allTime
      hN ha0 ha1 kappa beta g hbeta]
      with omega hsimpleSample hq hp
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)) := by
    simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using
      hsimpleSample
  intro time block
  let A := canonicalSignedAmplitudeEnvelope N kappa beta g hbeta
  let S := canonicalSignedSourceEnvelope N kappa beta g hbeta
  have hleg : ∀ i ∈ block,
      ‖canonicalSignedInteractionAmplitude (N := N)
        kappa beta g hbeta a (entry i) (omega, time)‖ ≤ A := by
    intro i _hi
    exact norm_canonicalSignedInteractionAmplitude_le_envelope_of_simple
      kappa beta g hbeta a omega hsimple (entry i) (hpositive i)
      time (hq time) (hp time)
  have hsource : ∀ i ∈ block,
      ‖canonicalSignedRotatedSource (N := N)
        kappa beta g hbeta a (entry i) (omega, time)‖ ≤ S := by
    intro i _hi
    exact norm_canonicalSignedRotatedSource_le_envelope_of_simple
      kappa beta g hbeta a omega hsimple (entry i) (hpositive i)
      time (hq time)
  constructor
  · simpa [canonicalSignedBlockObservable, A] using
      norm_finite_signed_block_le
        (fun i => canonicalSignedInteractionAmplitude (N := N)
          kappa beta g hbeta a (entry i) (omega, time)) block
        (canonicalSignedAmplitudeEnvelope_nonneg kappa beta g hbeta) hleg
  · simpa [canonicalSignedBlockInsertion, A, S] using
      norm_finite_signed_insertion_le
        (fun i => canonicalSignedInteractionAmplitude (N := N)
          kappa beta g hbeta a (entry i) (omega, time))
        (fun i => canonicalSignedRotatedSource (N := N)
          kappa beta g hbeta a (entry i) (omega, time)) block
        (canonicalSignedAmplitudeEnvelope_nonneg kappa beta g hbeta)
        (canonicalSignedSourceEnvelope_nonneg kappa beta g hbeta)
        hleg hsource

theorem integrable_canonicalSignedBlock_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
        kappa beta g hbeta a entry block (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    (aestronglyMeasurable_canonicalSignedBlock_fixedTime
      (N := N) kappa beta g hbeta a entry block time)
    (canonicalSignedBlockEnvelope
      (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta) block)
  filter_upwards [canonicalSignedBlockBounds_ae_allTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive] with omega hbound
  exact (hbound time block).1

theorem integrable_canonicalSignedBlockInsertion_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockInsertion (N := N)
        kappa beta g hbeta a entry block (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    (aestronglyMeasurable_canonicalSignedBlockInsertion_fixedTime
      (N := N) kappa beta g hbeta a entry block time)
    (canonicalSignedBlockInsertionEnvelope
      (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
      (canonicalSignedSourceEnvelope N kappa beta g hbeta) block)
  filter_upwards [canonicalSignedBlockBounds_ae_allTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive] with omega hbound
  exact (hbound time block).2

theorem hasCanonicalSignedBlockLocalDerivativeEnvelope_actual
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real) :
    HasCanonicalSignedBlockLocalDerivativeEnvelope (N := N)
      kappa beta g hbeta a entry block time 1
      (canonicalSignedBlockInsertionEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedSourceEnvelope N kappa beta g hbeta) block) := by
  refine ⟨zero_lt_one, ?_, ?_⟩
  · unfold canonicalSignedBlockInsertionEnvelope
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg block.card) (by
        unfold canonicalSignedBlockEnvelope
        exact pow_nonneg (by
          linarith [canonicalSignedAmplitudeEnvelope_nonneg
            (N := N) kappa beta g hbeta]) block.card))
      (canonicalSignedSourceEnvelope_nonneg kappa beta g hbeta)
  · filter_upwards [canonicalSignedBlockBounds_ae_allTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive] with omega hbound
    intro s _hs
    exact (hbound s block).2

/-- The completed actual-specific derivative-under-expectation theorem.  No
abstract envelope or base-time integrability premise remains. -/
theorem hasDerivAt_canonicalSignedBlockBochnerIntegral_actual
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real) :
    HasDerivAt
      (canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta g hbeta a entry block)
      (canonicalSignedBlockInsertionBochnerIntegral (N := N)
        kappa beta g hbeta a entry block time) time := by
  exact hasDerivAt_canonicalSignedBlockBochnerIntegral
    hN ha0 ha1 kappa beta g hbeta entry hpositive block time 1
    (canonicalSignedBlockInsertionEnvelope
      (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
      (canonicalSignedSourceEnvelope N kappa beta g hbeta) block)
    (hasCanonicalSignedBlockLocalDerivativeEnvelope_actual
      hN ha0 ha1 kappa beta g hbeta entry hpositive block time)
    (integrable_canonicalSignedBlock_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive block time)

end

end ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
