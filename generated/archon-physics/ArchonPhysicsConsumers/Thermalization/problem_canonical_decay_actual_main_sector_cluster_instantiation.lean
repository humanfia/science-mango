import ArchonPhysics.CanonicalDecayActualMainSectorClusterInstantiation

open scoped ENNReal Topology

namespace ArchonPhysicsConsumers.Thermalization.CanonicalDecayActualMainSectorClusterInstantiation

open ArchonPhysics
open ArchonPhysics.CanonicalChildRepeatedAnnealedAtlasSmallBall
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalDecayActualMainSectorClusterInstantiation
open ArchonPhysics.CanonicalDecayAnnealedSectorVolumeDomination
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.DecayChannelSectorClusterDecomposition
open ArchonPhysics.DecaySectorAnnealedClusterBridge
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open Filter MeasureTheory

noncomputable section

/-- The actual three-mass all-distinct coarea data and actual two-mass
child-repeated atlas data instantiate both scalar main sectors of a genuine
canonical decay cluster. -/
theorem actual_mainSector_cluster_volumeDomination
    {omega : RandomEnsemble.SampleSpace}
    {target : FiniteMeasure Real}
    {cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega target}
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (allDistinct : ActualThreeMassAllDistinctAnnealedRawCoareaSequence)
    (childRepeated : ActualTwoMassChildRepeatedAnnealedAtlasSequence) :
    (cluster.allDistinct : Measure Real) ≤
        (canonicalDecaySectorAnnealed_allDistinct_volumeDomination_of_actualCoarea
          allDistinct).constant • (volume : Measure Real) ∧
      (cluster.childRepeated : Measure Real) ≤
        (canonicalDecaySectorAnnealed_childRepeated_volumeDomination_of_actualAtlas
          childRepeated).constant • (volume : Measure Real) :=
  canonicalDecayCluster_mainSectorDomination_of_actualAtlases
    identification allDistinct childRepeated

/-- The same actual data close the complete decay broadened-mass upper
consumer; the two parent--child sectors are handled by their already proved
fractional decay. -/
theorem actual_mainSector_atlases_eventually_bound_complete_decay_mass
    (omega : RandomEnsemble.SampleSpace)
    (cluster : DecaySectorClusterDecomposition
      canonicalIIDMassPhaseEnsemble omega
      (canonicalCollisionPerSiteMeasureLimit canonicalIIDMassPhaseEnsemble
        decayInteractionSign))
    (identification :
      CanonicalMainDecaySectorsAnnealedClusterIdentification cluster)
    (allDistinct : ActualThreeMassAllDistinctAnnealedRawCoareaSequence)
    (childRepeated : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (time : Nat → Real) (htime_pos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop) :
    ∀ᶠ n in atTop,
      (canonicalBroadenedCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble decayInteractionSign
        (time n) (htime_pos n)).mass ≤
      (canonicalDecaySectorAnnealed_allDistinct_volumeDomination_of_actualCoarea
        allDistinct).constant.toNNReal +
      (canonicalDecaySectorAnnealed_childRepeated_volumeDomination_of_actualAtlas
        childRepeated).constant.toNNReal + 1 :=
  canonicalBroadenedCollisionPerSiteMeasureLimit_eventually_mass_le_of_actualMainSectorAtlases
    omega cluster identification allDistinct childRepeated
    time htime_pos htime

end

end ArchonPhysicsConsumers.Thermalization.CanonicalDecayActualMainSectorClusterInstantiation
