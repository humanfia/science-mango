import ArchonPhysics.ActualTwoMassChildRepeatedAnnealedLInfinity
import ArchonPhysics.CanonicalDecayAnnealedSmallBallCertificate
import ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit

/-!
# Canonical child-repeated annealed sector bridge

The scalar `ChildRepeated` sector barycenter is exactly the decay-mismatch
pushforward of the genuine annealed parent/child frequency law used by the
two-mass spectral-averaging modules.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalChildRepeatedAnnealedSectorBridge

open ArchonPhysics
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedCanonicalSubsequenceLimit
open ArchonPhysics.ChildRepeatedCanonicalWeakLimitBridge
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.DecayChannelMismatchSectorWeakLimit
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory Set

noncomputable section

/-- Exact finite-sample alignment of the reduced child law with the scalar
decay sector. -/
theorem canonicalChildRepeatedReducedPerSite_map_decay_eq_sector
    (n : Nat) (omega : RandomEnsemble.SampleSpace) :
    (((canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble n omega).map
        forgetRankFrequencyTriple).map childRepeatedFrequencyProjection).map
        childRepeatedDecayMismatch =
      canonicalDecaySectorPerSiteMismatchFiniteMeasure
        canonicalIIDMassPhaseEnsemble
        (fun {_N} _inst ↦ ChildRepeated) n omega := by
  rw [map_canonicalChildRepeatedRankFrequencyPerSiteFiniteMeasure_forgetRank]
  calc
    ((canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble n omega).map
        childRepeatedFrequencyProjection).map childRepeatedDecayMismatch =
      (canonicalChildRepeatedFrequencyPerSiteFiniteMeasure
          canonicalIIDMassPhaseEnsemble n omega).map
        (frequencyTripleMismatch decayInteractionSign) := by
          simpa only [canonicalChildRepeatedFrequencyPerSiteFiniteMeasure] using
            (perSiteChildRepeatedFiniteMeasure_decayMismatch_eq_reduced
              (canonicalIIDMassPhaseEnsemble.restrictPositiveMass
                (N := n + 2) omega)).symm
    _ = _ :=
      map_canonicalChildRepeatedFrequencyPerSiteFiniteMeasure_decay_eq_sector
        canonicalIIDMassPhaseEnsemble n omega

/-- Barycentering commutes with the exact finite-sample child mismatch
identity, so the annealed scalar sector is precisely the pushforward of the
annealed reduced law. -/
theorem canonicalDecaySectorAnnealed_childRepeated_eq_map_reduced
    (n : Nat) :
    canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure
        (fun {_N} _inst ↦ ChildRepeated) n =
      (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n).map
        childRepeatedDecayMismatch := by
  apply FiniteMeasure.toMeasure_injective
  ext A hA
  rw [canonicalDecaySectorAnnealedPerSiteMismatchFiniteMeasure_apply
    (fun {_N} _inst ↦ ChildRepeated) n hA]
  rw [FiniteMeasure.toMeasure_map,
    Measure.map_apply measurable_childRepeatedDecayMismatch hA]
  rw [canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply n
    (measurable_childRepeatedDecayMismatch hA)]
  apply lintegral_congr
  intro omega
  have hsample := canonicalChildRepeatedReducedPerSite_map_decay_eq_sector
    n omega
  have happ := congrArg (fun measure : FiniteMeasure Real ↦
    (measure : Measure Real) A) hsample
  simpa only [FiniteMeasure.toMeasure_map,
    Measure.map_apply measurable_childRepeatedDecayMismatch hA] using happ.symm

end


end ArchonPhysics.CanonicalChildRepeatedAnnealedSectorBridge
