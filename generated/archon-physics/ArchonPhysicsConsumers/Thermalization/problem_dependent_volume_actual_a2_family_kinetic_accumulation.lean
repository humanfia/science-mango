import ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation

/-!
Consumer for actual-A2 families in which the active finite volume depends on
the channel index and may therefore vary with the external weak parameter `g`.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation
open Filter
open scoped BigOperators Topology

noncomputable section

example {Index Omega : Type*} [MeasurableSpace Omega]
    (indices : Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble) :
    Tendsto
      (fun g => ∑ index ∈ indices,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_finset_dependentActualA2ExternalWeakCouplingAccumulation indices
    ensemble datum certificate

example {Index Omega : Type*} [MeasurableSpace Omega]
    (active : Real -> Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble)
    (costEnvelope : Real -> Real)
    (hcostEnvelope : ∀ᶠ g in 𝓝[>] (0 : Real),
      (∑ index ∈ active g,
        (datum index).compactKineticCost ensemble (certificate index)) <=
          costEnvelope g)
    (hscaledEnvelope : Tendsto
      (fun g => weakCouplingLogarithmicFactor g *
        costEnvelope g)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growing_dependentActualA2ExternalWeakCouplingAccumulation_of_costEnvelope
    active ensemble datum certificate costEnvelope hcostEnvelope
      hscaledEnvelope

example {Index Omega : Type*} [MeasurableSpace Omega]
    (volumeSchedule : Real -> Nat) (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (hvolume : ActiveFamilyMatchesVolumeSchedule volumeSchedule active datum)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble)
    (uniformCost : Real -> Real)
    (huniformCost : ∀ᶠ g in 𝓝[>] (0 : Real),
      ∀ index ∈ active g,
        (datum index).compactKineticCost ensemble (certificate index) <=
          uniformCost g)
    (hscaledCardCost : Tendsto
      (fun g => weakCouplingLogarithmicFactor g *
        ((active g).card : Real) * uniformCost g)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_volumeScheduled_dependentActualA2ExternalWeakCouplingAccumulation
    volumeSchedule active ensemble datum hvolume certificate uniformCost
      huniformCost hscaledCardCost

end

end ArchonPhysicsConsumers.Thermalization
