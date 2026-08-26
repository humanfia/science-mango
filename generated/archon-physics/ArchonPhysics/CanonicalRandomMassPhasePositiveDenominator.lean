import ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
import ArchonPhysics.PositiveHarmonicEnergyAlongCoerciveFlow

/-!
# Positive normalization denominator for the canonical frozen observable

The canonical random-mass/random-phase late-window observable uses one
sample-independent global flow.  On the almost-sure simple-spectrum locus,
that flow agrees at every real time with the genuine reduced Hamiltonian
trajectory from the frozen unit-harmonic-energy initial state.  Strict
coercivity therefore makes the positive-mode late-window total strictly
positive on every nondegenerate window.

This removes the totalized zero-denominator branch from the canonical frozen
observable almost surely.  In particular, its normalized positive-mode
weights sum exactly to one.  No hitting-time finiteness, kinetic limit, or
`g⁻²` scaling conclusion is asserted.
-/

namespace ArchonPhysics.CanonicalRandomMassPhasePositiveDenominator

open ArchonPhysics
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CanonicalRandomMassPhaseThermalizationObservable
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.PhysicalHarmonicEnergyIdentity
open ArchonPhysics.PositiveHarmonicEnergyAlongCoerciveFlow
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPhaseLateWindowObservable
open ArchonPhysics.RandomMassPositiveLateWindowObservable
open ArchonPhysics.RandomMassReducedPhaseInitialData
open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Total positive-mode late-window weight of the canonical frozen random
observable. -/
def canonicalFrozenPositiveLateWindowTotalWeight
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu T : Real) : RandomEnsemble.SampleSpace → Real :=
  sampledPositiveLateWindowTotalWeight
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a)
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta) mu T

/-- Positive-mode late-window weights of the canonical frozen observable,
normalized by their total. -/
def canonicalFrozenPositiveLateWindowNormalizedWeights
    {N : Nat} [NeZero N]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a mu T : Real) (omega : RandomEnsemble.SampleSpace) :
    OrderedModeIndex N → Real :=
  sampledPositiveLateWindowNormalizedWeights
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
    (canonicalPhaseInitialSample (N := N) kappa beta g a)
    (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta) mu T omega

/-- The frozen reduced initial state has exactly unit physical harmonic
energy on every simple-spectrum realization. -/
theorem reducedPhysicalHarmonicEnergy_reducedInitialStateOfSimple_eq_one
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (omega : Omega)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (ensemble.restrictPositiveMass (N := N) omega))) :
    reducedPhysicalHarmonicEnergy
        (ensemble.restrictPositiveMass (N := N) omega)
        (reducedInitialStateOfSimple ensemble a omega hsimple) = 1 := by
  let m := ensemble.restrictPositiveMass (N := N) omega
  have hmodal :
      (∑ k : OrderedModeIndex N,
        harmonicOrderedPhysicalModeEnergy
          (ensemble.restrictPositiveMass (N := N))
          (initialPhysicalPosition ensemble a)
          (initialPhysicalMomentum ensemble a) omega k) = 1 := by
    calc
      (∑ k : OrderedModeIndex N,
        harmonicOrderedPhysicalModeEnergy
          (ensemble.restrictPositiveMass (N := N))
          (initialPhysicalPosition ensemble a)
          (initialPhysicalMomentum ensemble a) omega k) =
          ∑ k : OrderedModeIndex N, orderedTargetEnergy N a k := by
        apply Finset.sum_congr rfl
        intro k _hk
        exact harmonicOrderedPhysicalModeEnergy_initial_eq_target
          ensemble hN ha0 ha1 omega hsimple k
      _ = 1 := sum_orderedTargetEnergy_eq_one hN a
  have hharmonic :
      physicalHarmonicHamiltonian m
        (initialPhysicalMomentum ensemble a omega)
        (initialPhysicalPosition ensemble a omega) = 1 := by
    rw [← hmodal]
    exact (sum_harmonicOrderedPhysicalModeEnergy_eq_physical_of_simple
      (ensemble.restrictPositiveMass (N := N))
      (initialPhysicalPosition ensemble a)
      (initialPhysicalMomentum ensemble a) omega
      (by simpa [harmonicHermitianSample, harmonicHermitian, m] using
        hsimple)).symm
  unfold reducedPhysicalHarmonicEnergy reducedInitialStateOfSimple
  change physicalHarmonicHamiltonian m
    (WithLp.ofLp (initialPhysicalMomentum ensemble a omega))
    (WithLp.ofLp (initialPhysicalPosition ensemble a omega)) = 1
  exact hharmonic

variable {S : Type*}

/-- For a mass family which may vary away from the selected sample, an
all-time ambient/reduced match identifies the selected late-window total with
the genuine reduced-path total. -/
theorem sampledPositiveLateWindowTotalWeight_eq_reduced_at_of_match
    {N : Nat} [NeZero N]
    (massSample : S → Lattice.PositiveMassConfig N)
    (initial : S → ParametricPhaseSpace N)
    (flow : ParametricPhaseSpace N × Real → ParametricPhaseSpace N)
    (kappa beta g : Real) (s : S)
    (z : Real → ReducedPhaseSpace (massSample s))
    (hmatch : ∀ t, flow (initial s, t) =
      embedReducedPoint (massSample s) kappa beta g (z t))
    (mu T : Real) :
    sampledPositiveLateWindowTotalWeight massSample initial flow mu T s =
      reducedPositiveLateWindowTotalWeight (massSample s) z mu T := by
  unfold sampledPositiveLateWindowTotalWeight
    sampledPositiveLateWindowAverage reducedPositiveLateWindowTotalWeight
    totalWeight lateWindowAverage
  apply Finset.sum_congr rfl
  intro k _hk
  change ((1 - mu) * T)⁻¹ *
      (∫ t in mu * T..T,
        sampledPositivePhysicalOrderedEnergyProfileAlongFlow
          massSample initial flow (s, t) k) =
    ((1 - mu) * T)⁻¹ *
      (∫ t in mu * T..T,
        reducedPositiveOrderedEnergyProfile (massSample s) z t k)
  congr 1
  apply intervalIntegral.integral_congr
  intro t _ht
  unfold sampledPositivePhysicalOrderedEnergyProfileAlongFlow
    reducedPositiveOrderedEnergyProfile
  change (if k ∈ positiveModeIndices (harmonicHermitian (massSample s)) then
      sampledPhysicalOrderedModeEnergyAlongFlow
        massSample initial flow (s, t) k else 0) =
    if k ∈ positiveModeIndices (harmonicHermitian (massSample s)) then
      reducedPhysicalOrderedModeEnergy (massSample s) (z t) k else 0
  split_ifs with hk
  · exact sampledPhysicalOrderedModeEnergyAlongFlow_eq_reduced_at
      massSample initial flow kappa beta g s z hmatch t k
  · rfl

/-- On a simple realization, every nondegenerate canonical late window has a
strictly positive positive-mode normalization denominator. -/
theorem canonicalFrozenPositiveLateWindowTotalWeight_pos_of_simple
    {N : Nat} [NeZero N]
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : RandomEnsemble.SampleSpace)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)))
    (mu T : Real) (hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T) :
    0 < canonicalFrozenPositiveLateWindowTotalWeight
      (N := N) kappa beta g hbeta a mu T omega := by
  obtain ⟨z, hz0, hz, hmatch, _hmode, _hl1⟩ :=
    canonicalFrozenLateWindowL1Distance_matches_reduced_of_simple
      hN ha0 ha1 kappa beta g hbeta omega hsimple mu T
  have hunit : reducedPhysicalHarmonicEnergy
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
        (N := N) omega)
      (reducedInitialStateOfSimple
        canonicalIIDMassPhaseEnsemble a omega hsimple) = 1 :=
    reducedPhysicalHarmonicEnergy_reducedInitialStateOfSimple_eq_one
      canonicalIIDMassPhaseEnsemble hN ha0 ha1 omega hsimple
  rw [canonicalFrozenPositiveLateWindowTotalWeight,
    sampledPositiveLateWindowTotalWeight_eq_reduced_at_of_match
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g a)
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta)
      kappa beta g omega z hmatch mu T]
  exact reducedPositiveLateWindowTotalWeight_pos
    (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N) omega)
    hbeta g
    (reducedInitialStateOfSimple
      canonicalIIDMassPhaseEnsemble a omega hsimple)
    z hz0 hz hunit hsimple mu T hmu hmuOne hT

/-- The canonical positive-mode late-window denominator is strictly positive
almost surely. -/
theorem canonicalFrozenPositiveLateWindowTotalWeight_pos_ae
    {N : Nat} [NeZero N]
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu T : Real) (hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      0 < canonicalFrozenPositiveLateWindowTotalWeight
        (N := N) kappa beta g hbeta a mu T omega := by
  have hsimpleAE :=
    RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
      (N := N) canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega)
  filter_upwards [hsimpleAE] with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian
        (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
          (N := N) omega)) := by
    simpa [harmonicHermitianSample, harmonicHermitian] using hsimpleSample
  exact canonicalFrozenPositiveLateWindowTotalWeight_pos_of_simple
    hN ha0 ha1 kappa beta g hbeta omega hsimple mu T hmu hmuOne hT

/-- Almost surely, the canonical normalized positive-mode late-window weights
sum exactly to one. -/
theorem sum_canonicalFrozenPositiveLateWindowNormalizedWeights_ae
    {N : Nat} [NeZero N]
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (mu T : Real) (hmu : 0 ≤ mu) (hmuOne : mu < 1) (hT : 0 < T) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      (∑ k : OrderedModeIndex N,
        canonicalFrozenPositiveLateWindowNormalizedWeights
          (N := N) kappa beta g hbeta a mu T omega k) = 1 := by
  filter_upwards [canonicalFrozenPositiveLateWindowTotalWeight_pos_ae
    hN ha0 ha1 kappa beta g hbeta mu T hmu hmuOne hT] with omega hpositive
  exact sum_normalizedWeights
    (sampledPositiveLateWindowAverage
      (canonicalIIDMassPhaseEnsemble.restrictPositiveMass (N := N))
      (canonicalPhaseInitialSample (N := N) kappa beta g a)
      (canonicalRandomMassPhaseGlobalFlow N kappa beta g hbeta) mu T omega)
    hpositive

end

end ArchonPhysics.CanonicalRandomMassPhasePositiveDenominator
