import ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter

/-!
# Closing the actual canonical iid expectation envelope

This file applies the explicit finite-dimensional norm constants from
`CanonicalIIDCoerciveActualExpectationAdapter` to the actual canonical
alpha--beta orbit, its measurable ordered modes, arbitrary fixed signed
blocks, and their exact one-slot source insertions.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
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
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory
open Metric

noncomputable section

variable {N : Nat} [NeZero N]

theorem canonicalMass_lower (omega : CanonicalSample) (i : Lattice.Site N) :
    (4 / 5 : Real) ≤ (canonicalMass (N := N) omega).mass i := by
  simpa [canonicalMass, RandomEnsemble.massLower] using
    (canonicalIIDMassPhaseEnsemble.mass_mem_support i.val omega).1

theorem canonicalMass_upper (omega : CanonicalSample) (i : Lattice.Site N) :
    (canonicalMass (N := N) omega).mass i ≤ (6 / 5 : Real) := by
  simpa [canonicalMass, RandomEnsemble.massUpper] using
    (canonicalIIDMassPhaseEnsemble.mass_mem_support i.val omega).2

theorem canonicalOrderedFrequency_pos
    (k : OrderedModeIndex N)
    (hk : k ≠ lastOrderedIndex (ι := Lattice.Site N))
    (omega : CanonicalSample) :
    0 < canonicalOrderedFrequency (N := N) k omega := by
  exact (CanonicalCollisionSoftLegBound.orderedModeFrequency_pos_iff_ne_last_unconditional
      (canonicalMass (N := N) omega) k).2 hk

theorem canonicalOrderedFrequency_le_sqrt_five
    (k : OrderedModeIndex N) (omega : CanonicalSample) :
    canonicalOrderedFrequency (N := N) k omega ≤ Real.sqrt 5 := by
  exact iid_orderedModeFrequency_harmonic_le_sqrt_five
    canonicalIIDMassPhaseEnsemble omega k

theorem canonicalPositiveFrequencyNormalizationEnvelope_nonneg :
    0 ≤ canonicalPositiveFrequencyNormalizationEnvelope N := by
  unfold canonicalPositiveFrequencyNormalizationEnvelope
  positivity

/-- The finite-volume infrared estimate in exactly the square-root
normalization used by both amplitudes and forced sources. -/
theorem inv_sqrt_two_mul_canonicalOrderedFrequency_le_envelope
    (k : OrderedModeIndex N)
    (hk : k ≠ lastOrderedIndex (ι := Lattice.Site N))
    (omega : CanonicalSample) :
    (Real.sqrt (2 * canonicalOrderedFrequency (N := N) k omega))⁻¹ ≤
      canonicalPositiveFrequencyNormalizationEnvelope N := by
  have hNpos : (0 : Real) < N := by exact_mod_cast (NeZero.pos N)
  have hwpos := canonicalOrderedFrequency_pos k hk omega
  have hinv := inv_canonicalOrderedFrequency_le_volume k hk omega
  have hNinv : (N : Real)⁻¹ ≤
      canonicalOrderedFrequency (N := N) k omega := by
    simpa using
      ((inv_le_inv₀ hNpos (inv_pos.mpr hwpos)).2 hinv)
  have harg : 2 * (N : Real)⁻¹ ≤
      2 * canonicalOrderedFrequency (N := N) k omega := by
    exact mul_le_mul_of_nonneg_left hNinv (by norm_num)
  have hsqrt : Real.sqrt (2 * (N : Real)⁻¹) ≤
      Real.sqrt (2 * canonicalOrderedFrequency (N := N) k omega) :=
    Real.sqrt_le_sqrt harg
  have hleft : 0 < Real.sqrt (2 * (N : Real)⁻¹) := by positivity
  have hright : 0 < Real.sqrt
      (2 * canonicalOrderedFrequency (N := N) k omega) := by positivity
  unfold canonicalPositiveFrequencyNormalizationEnvelope
  exact (inv_le_inv₀ hright hleft).2 hsqrt

theorem norm_sqrtMassTransform_canonical_le_envelope
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : CanonicalSample) (q : HilbertConfiguration N)
    (hq : ‖q‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius) :
    ‖sqrtMassTransform (canonicalMass (N := N) omega) q‖ ≤
      canonicalWeightedCoordinateEnvelope N kappa beta g hbeta := by
  calc
    ‖sqrtMassTransform (canonicalMass (N := N) omega) q‖ ≤ 2 * ‖q‖ :=
      norm_sqrtMassTransform_le_two_mul _ (canonicalMass_upper omega) q
    _ ≤ 2 * canonicalNonnegativeShellRadius N kappa beta g hbeta := by
      gcongr
      exact hq.trans (le_max_left _ _)
    _ = canonicalWeightedCoordinateEnvelope N kappa beta g hbeta := rfl

theorem norm_inverseSqrtMassTransform_canonical_le_envelope
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : CanonicalSample) (p : HilbertConfiguration N)
    (hp : ‖p‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius) :
    ‖inverseSqrtMassTransform (canonicalMass (N := N) omega) p‖ ≤
      canonicalWeightedCoordinateEnvelope N kappa beta g hbeta := by
  calc
    ‖inverseSqrtMassTransform (canonicalMass (N := N) omega) p‖ ≤ 2 * ‖p‖ :=
      norm_inverseSqrtMassTransform_le_two_mul _ (canonicalMass_lower omega) p
    _ ≤ 2 * canonicalNonnegativeShellRadius N kappa beta g hbeta := by
      gcongr
      exact hp.trans (le_max_left _ _)
    _ = canonicalWeightedCoordinateEnvelope N kappa beta g hbeta := rfl

theorem abs_forwardDifference_le_two_mul_norm
    (q : HilbertConfiguration N) (i : Lattice.Site N) :
    |Lattice.forwardDifference (asConfiguration q) i| ≤ 2 * ‖q‖ := by
  rw [Lattice.forwardDifference_apply]
  calc
    |asConfiguration q (i + 1) - asConfiguration q i| ≤
        |asConfiguration q (i + 1)| + |asConfiguration q i| := abs_sub _ _
    _ ≤ ‖q‖ + ‖q‖ := by
      apply add_le_add
      · simpa only [asConfiguration, Real.norm_eq_abs] using
          (PiLp.norm_apply_le q (i + 1))
      · simpa only [asConfiguration, Real.norm_eq_abs] using
          (PiLp.norm_apply_le q i)
    _ = 2 * ‖q‖ := by ring

theorem abs_nonlinearPotentialDerivative_le_envelope
    (kappa beta g x B : Real) (hB : |x| ≤ B) :
    |nonlinearPotentialDerivative kappa beta g x| ≤
      canonicalNonlinearBondDerivativeEnvelope kappa beta g B := by
  have hB0 : 0 ≤ B := (abs_nonneg x).trans hB
  unfold nonlinearPotentialDerivative
    canonicalNonlinearBondDerivativeEnvelope
  calc
    |kappa * g * x ^ 2 + beta * g ^ 2 * x ^ 3| ≤
        |kappa * g * x ^ 2| + |beta * g ^ 2 * x ^ 3| := abs_add_le _ _
    _ = |kappa * g| * |x| ^ 2 + |beta * g ^ 2| * |x| ^ 3 := by
      simp only [abs_mul, abs_pow]
    _ ≤ |kappa * g| * B ^ 2 + |beta * g ^ 2| * B ^ 3 := by
      gcongr

end

end ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
