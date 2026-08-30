import ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
import ArchonPhysics.WeakCouplingA2ChannelFamilyExplicitGrowthThreshold

/-!
# Explicit thermodynamic-growth threshold for actual A2 families

This module combines the dependent-volume actual-channel interface with the
explicit weak-coupling power threshold.  If the active channel count is
`O(g ^ (-p))` and the largest compact-certificate cost is `O(g ^ (-q))`, the
externally scaled `g^2 A2(kappa)` family vanishes on the `g^-2` window whenever
`p + q < 2`.

The theorem permits a genuinely growing volume schedule.  It does not prove
the model-specific cardinality or certificate-cost envelopes.
-/

namespace ArchonPhysics.DependentVolumeActualA2ExplicitGrowthThreshold

open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.WeakCouplingA2ChannelFamilyExplicitGrowthThreshold
open Filter
open scoped BigOperators Topology

noncomputable section

/-- Explicit power-law sufficient condition for a growing family of actual
dependent-volume A2 channels.  Each datum keeps its base `kappa` fixed; `g`
is the only weak variable. -/
theorem
    tendsto_growing_dependentActualA2ExternalWeakCoupling_of_rpow_envelopes
    {Index Omega : Type*} [MeasurableSpace Omega]
    (active : Real -> Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble)
    (uniformCost : Real -> Real)
    (cardExponent costExponent cardConstant costConstant : Real)
    (hexponents : cardExponent + costExponent < 2)
    (hcardConstant : 0 <= cardConstant)
    (huniformCost : ∀ᶠ g in 𝓝[>] (0 : Real),
      ∀ index ∈ active g,
        (datum index).compactKineticCost ensemble (certificate index) <=
          uniformCost g)
    (hcard : ∀ᶠ g in 𝓝[>] (0 : Real),
      ((active g).card : Real) <= cardConstant * g ^ (-cardExponent))
    (hcostNonneg : ∀ᶠ g in 𝓝[>] (0 : Real),
      0 <= uniformCost g)
    (hcost : ∀ᶠ g in 𝓝[>] (0 : Real),
      uniformCost g <= costConstant * g ^ (-costExponent)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) := by
  apply
    tendsto_growing_dependentActualA2ExternalWeakCouplingAccumulation_of_card_uniformCost
      active ensemble datum certificate uniformCost huniformCost
  exact
    tendsto_logarithmicFactor_mul_card_mul_uniformCost_of_rpow_envelopes
      active uniformCost cardExponent costExponent cardConstant costConstant
      hexponents hcardConstant hcard hcostNonneg hcost

/-- Schedule-facing form.  The active datum volumes may follow any declared
`volumeSchedule`; the displayed power envelopes state the remaining uniform
thermodynamic estimate explicitly. -/
theorem
    tendsto_volumeScheduled_dependentActualA2ExternalWeakCoupling_of_rpow_envelopes
    {Index Omega : Type*} [MeasurableSpace Omega]
    (volumeSchedule : Real -> Nat) (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (_hvolume : ActiveFamilyMatchesVolumeSchedule volumeSchedule active datum)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble)
    (uniformCost : Real -> Real)
    (cardExponent costExponent cardConstant costConstant : Real)
    (hexponents : cardExponent + costExponent < 2)
    (hcardConstant : 0 <= cardConstant)
    (huniformCost : ∀ᶠ g in 𝓝[>] (0 : Real),
      ∀ index ∈ active g,
        (datum index).compactKineticCost ensemble (certificate index) <=
          uniformCost g)
    (hcard : ∀ᶠ g in 𝓝[>] (0 : Real),
      ((active g).card : Real) <= cardConstant * g ^ (-cardExponent))
    (hcostNonneg : ∀ᶠ g in 𝓝[>] (0 : Real),
      0 <= uniformCost g)
    (hcost : ∀ᶠ g in 𝓝[>] (0 : Real),
      uniformCost g <= costConstant * g ^ (-costExponent)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growing_dependentActualA2ExternalWeakCoupling_of_rpow_envelopes
    active ensemble datum certificate uniformCost cardExponent costExponent
    cardConstant costConstant hexponents hcardConstant huniformCost hcard
    hcostNonneg hcost

end

end ArchonPhysics.DependentVolumeActualA2ExplicitGrowthThreshold
