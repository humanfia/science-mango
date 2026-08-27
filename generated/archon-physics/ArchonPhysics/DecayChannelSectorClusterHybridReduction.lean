import ArchonPhysics.ChildRepeatedScalarClusterHybridLift
import ArchonPhysics.DecayChannelSectorClusterDecomposition

/-!
# Hybrid reduction of the canonical decay-sector cluster

The common four-sector scalar cluster is combined with a marked hybrid lift
of its child-repeated member.  Consequently the exact-resonance atom of the
full decay collision limit is reduced, without changing subsequences, to two
and only two boundary statements:

* the all-distinct scalar cluster has no zero atom;
* the reduced child law does not charge `omega_parent = 2 * omega_child`.

This module records the exact reduction.  It does not assume either remaining
nullity statement.
-/

open scoped Topology

namespace ArchonPhysics.DecayChannelSectorClusterHybridReduction

open ArchonPhysics
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalCollisionPerSiteMeasureFourier
open ArchonPhysics.CanonicalComplexSpectralPolynomialMomentAllVolume
open ArchonPhysics.ChildRepeatedCanonicalClusterLimit
open ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit
open ArchonPhysics.ChildRepeatedScalarClusterHybridLift
open ArchonPhysics.DecayChannelSectorClusterDecomposition
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A common scalar sector decomposition together with a marked hybrid lift
of its child-repeated member along the very same volume subsequence (up to the
cofinal subsubsequence stored by the lift). -/
structure DecaySectorClusterHybridReductionData
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure Real) where
  cluster : DecaySectorClusterDecomposition ensemble omega target
  childLift : ChildRepeatedScalarClusterHybridLiftData
    ensemble omega cluster.subsequence cluster.childRepeated

/-- Exact endpoint of the sector reduction: the full zero atom vanishes iff
the all-distinct cluster has no zero atom and the reduced child law gives zero
mass to the resonance line. -/
theorem DecaySectorClusterHybridReductionData.target_zeroAtom_iff
    {ensemble : IIDMassPhaseEnsemble Omega} {omega : Omega}
    {target : FiniteMeasure Real}
    (reduction : DecaySectorClusterHybridReductionData
      ensemble omega target) :
    (target : Measure Real) ({0} : Set Real) = 0 ↔
      (reduction.cluster.allDistinct : Measure Real)
          ({0} : Set Real) = 0 ∧
      (((reduction.childLift.markedTarget.map
          CanonicalRankFrequencyMarkedMeasure.forgetRankFrequencyTriple).map
          ChildRepeatedDiagonalHybridKernel.childRepeatedFrequencyProjection :
          FiniteMeasure (Real × Real)) : Measure (Real × Real))
        childRepeatedReducedResonanceLine = 0 := by
  rw [reduction.cluster.target_zeroAtom_iff]
  exact and_congr_right fun _ =>
    reduction.childLift.scalar_singleton_zero_iff

/-- Simple spectrum and a supplied full collision weak limit produce the
combined scalar/marked hybrid reduction. -/
theorem exists_decaySectorClusterHybridReduction_of_simple_of_fullLimit
    (ensemble : IIDMassPhaseEnsemble Omega) (omega : Omega)
    (target : FiniteMeasure Real)
    (hsimple : forall n,
      SimpleOrderedSpectrum
        (harmonicHermitian
          (ensemble.restrictPositiveMass (N := n + 2) omega)))
    (hfull : Tendsto
      (fun n => canonicalCollisionPerSiteFiniteMeasure ensemble
        decayInteractionSign n omega)
      atTop (nhds target)) :
    Nonempty (DecaySectorClusterHybridReductionData
      ensemble omega target) := by
  obtain ⟨cluster⟩ :=
    exists_decaySectorClusterDecomposition_of_simple_of_fullLimit
      ensemble omega target hsimple hfull
  obtain ⟨childLift⟩ :=
    exists_childRepeatedScalarClusterHybridLift_of_simple
      ensemble omega cluster.subsequence cluster.childRepeated
      (fun j => hsimple (cluster.subsequence j))
      cluster.childRepeated_tendsto
  exact ⟨{
    cluster := cluster
    childLift := childLift }⟩

/-- For the frozen canonical iid ensemble, the deterministic full decay
collision limit admits the exact two-boundary hybrid reduction almost surely.
-/
theorem exists_canonicalDecaySectorClusterHybridReduction_ae :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Nonempty (DecaySectorClusterHybridReductionData
        canonicalIIDMassPhaseEnsemble omega
        (canonicalCollisionPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble decayInteractionSign)) := by
  filter_upwards
    [canonicalPositiveVolumes_simpleOrderedSpectrum_ae
      canonicalIIDMassPhaseEnsemble,
    canonicalCollisionPerSiteFiniteMeasure_tendsto_limit_ae
      canonicalIIDMassPhaseEnsemble decayInteractionSign]
      with omega hsimple hfull
  have hsimple' : forall n,
      SimpleOrderedSpectrum
        (harmonicHermitian
          (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
            (N := n + 2) omega)) := by
    intro n
    simpa [Nat.add_assoc] using hsimple (n + 1) (by omega)
  have hfull' : Tendsto
      (fun n => canonicalCollisionPerSiteFiniteMeasure
        canonicalIIDMassPhaseEnsemble decayInteractionSign n omega)
      atTop
      (nhds (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble decayInteractionSign)) :=
    (tendsto_add_atTop_iff_nat 1).mp hfull
  exact exists_decaySectorClusterHybridReduction_of_simple_of_fullLimit
    canonicalIIDMassPhaseEnsemble omega
    (canonicalCollisionPerSiteMeasureLimit
      canonicalIIDMassPhaseEnsemble decayInteractionSign)
    hsimple' hfull'

end

end ArchonPhysics.DecayChannelSectorClusterHybridReduction
