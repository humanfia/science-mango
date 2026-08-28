import ArchonPhysics.OrderedCounterrotatingStaticFluxVolumeBound
import ArchonPhysics.TruncatedGaussianMassPhaseEnsemble
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Consumer: linear-volume ordered counterrotating static flux

This consumer specializes the exact spectral-factorization bound to every
frozen sample of the v0.3 conditioned Gaussian mass ensemble.  The physical
band edge is `sqrt 5`; no acoustic lower gap is assumed.
-/

namespace ArchonPhysicsConsumers.Thermalization.OrderedCounterrotatingStaticFluxVolumeBound

open ArchonPhysics
open ArchonPhysics.OrderedCounterrotatingStaticFluxVolumeBound
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.TruncatedGaussianMassLaw
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

noncomputable section

/-- Frozen finite-volume positive mass configuration of one Gaussian sample. -/
def gaussianFrozenMass
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) :
    Lattice.PositiveMassConfig N :=
  ensemble.restrictPositiveMass sample

private theorem gaussianFrozenMass_lower
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) :
    ∀ i : Lattice.Site N, (4 / 5 : Real) ≤
      (gaussianFrozenMass (N := N) ensemble sample).mass i := by
  intro i
  simpa [gaussianFrozenMass, RandomEnsemble.massLower] using
    (ensemble.mass_mem_support i.val sample).1

/-- Every ordered harmonic frequency of a frozen Gaussian sample is at most
`sqrt 5`. -/
theorem gaussianSample_orderedModeFrequency_le_sqrt_five
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega)
    (k : OrderedModeIndex N) :
    orderedModeFrequency
        (harmonicHermitian
          (gaussianFrozenMass (N := N) ensemble sample)) k ≤
      Real.sqrt 5 := by
  simpa [RandomEnsemble.massLower] using
    orderedModeFrequency_harmonic_le_sqrt_four_div_massLower
      (gaussianFrozenMass (N := N) ensemble sample)
      (4 / 5 : Real) (by norm_num)
      (gaussianFrozenMass_lower (N := N) ensemble sample) k

/-- For every frozen Gaussian sample, the complete positive ordered all-plus
static flux, including the physical `4 kappa²` factor, is `O(N)` with the
explicit per-volume constant `(3/2) kappa² sqrt(5) Emax²`. -/
theorem gaussianSample_four_kappa_sq_mul_allPlusFlux_div_volume_le
    {Omega : Type*} [MeasurableSpace Omega] {parameters : Parameters}
    (ensemble : GaussianIIDMassPhaseEnsemble parameters Omega)
    {N : Nat} [NeZero N] (sample : Omega) (kappa : Real)
    (energy : OrderedModeIndex N → Real) (energyCeiling : Real)
    (henergyNonneg : ∀ k, 0 ≤ energy k)
    (henergy : ∀ k, energy k ≤ energyCeiling) :
    (4 * kappa ^ 2 *
        positiveOrderedAllPlusActionFluxSum
          (gaussianFrozenMass (N := N) ensemble sample) energy) /
        (N : Real) ≤
      (3 / 2 : Real) * kappa ^ 2 * Real.sqrt 5 * energyCeiling ^ 2 := by
  exact four_kappa_sq_mul_positiveOrderedAllPlusActionFluxSum_div_volume_le
    (gaussianFrozenMass (N := N) ensemble sample) kappa energy energyCeiling
    (Real.sqrt 5) henergyNonneg henergy (Real.sqrt_nonneg _)
    (gaussianSample_orderedModeFrequency_le_sqrt_five
      ensemble sample)

#print axioms gaussianSample_orderedModeFrequency_le_sqrt_five
#print axioms gaussianSample_four_kappa_sq_mul_allPlusFlux_div_volume_le

end

end ArchonPhysicsConsumers.Thermalization.OrderedCounterrotatingStaticFluxVolumeBound
