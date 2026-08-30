import ArchonPhysics.DependentVolumeActualA2ExplicitGrowthThreshold

/-! Consumer for the explicit growing-volume actual-A2 power threshold. -/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.DependentVolumeActualA2ExplicitGrowthThreshold
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open Filter
open scoped BigOperators Topology

noncomputable section

example {Index Omega : Type*} [MeasurableSpace Omega]
    (volumeSchedule : Real -> Nat) (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (hvolume : ActiveFamilyMatchesVolumeSchedule volumeSchedule active datum)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble)
    (uniformCost : Real -> Real)
    (p q cardConstant costConstant : Real)
    (hpq : p + q < 2) (hcardConstant : 0 <= cardConstant)
    (huniformCost : ∀ᶠ g in 𝓝[>] (0 : Real),
      ∀ index ∈ active g,
        (datum index).compactKineticCost ensemble (certificate index) <=
          uniformCost g)
    (hcard : ∀ᶠ g in 𝓝[>] (0 : Real),
      ((active g).card : Real) <= cardConstant * g ^ (-p))
    (hcostNonneg : ∀ᶠ g in 𝓝[>] (0 : Real),
      0 <= uniformCost g)
    (hcost : ∀ᶠ g in 𝓝[>] (0 : Real),
      uniformCost g <= costConstant * g ^ (-q)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_volumeScheduled_dependentActualA2ExternalWeakCoupling_of_rpow_envelopes
    volumeSchedule active ensemble datum hvolume certificate uniformCost p q
    cardConstant costConstant hpq hcardConstant huniformCost hcard hcostNonneg
    hcost

#print axioms
  tendsto_growing_dependentActualA2ExternalWeakCoupling_of_rpow_envelopes
#print axioms
  tendsto_volumeScheduled_dependentActualA2ExternalWeakCoupling_of_rpow_envelopes

end

end ArchonPhysicsConsumers.Thermalization
