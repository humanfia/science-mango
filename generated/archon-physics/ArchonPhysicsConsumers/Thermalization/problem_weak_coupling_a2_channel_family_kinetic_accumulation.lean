import ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation

/-!
Consumer for fixed finite and coupling-dependent growing families of
kinetically weighted A2 channels.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

example : Tendsto weakCouplingLogarithmicFactor
    (𝓝[>] 0) (𝓝 0) :=
  tendsto_weakCouplingLogarithmicFactor_nhdsGT_zero

example {Index : Type*}
    (indices : Finset Index) (family : Index -> Real -> Real)
    (hfamily : ∀ index ∈ indices,
      Tendsto (family index) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun coupling =>
      ∑ index ∈ indices, family index coupling)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_finset_sum_nhds_zero indices family hfamily

example {Index Omega : Type*}
    [MeasurableSpace Omega]
    (indices : Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (weight : Index -> Omega -> Complex)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ∀ index,
      ActualIteratedA2WeightedChannelC1L1Certificate ensemble
        (channel index) (weight index) (observed index) (term index)) :
    Tendsto
      (fun coupling => ∑ index ∈ indices,
        weakCouplingKineticAccumulation
          (actualIteratedA2WeightedChannelExpectation ensemble
            (channel index) (weight index) (observed index) (term index))
          coupling)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_finset_actualIteratedA2WeightedChannel_kineticAccumulation
    indices ensemble channel weight observed term certificate

example {Index Omega : Type*}
    [MeasurableSpace Omega]
    (indices : Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (weight : Index -> Omega -> Complex)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ∀ index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index) (weight index) (observed index) (term index)) :
    Tendsto
      (fun coupling => ∑ index ∈ indices,
        weakCouplingKineticAccumulation
          (actualIteratedA2WeightedChannelExpectation ensemble
            (channel index) (weight index) (observed index) (term index))
          coupling)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_finset_actualIteratedA2WeightedChannel_compact_kineticAccumulation
    indices ensemble channel weight observed term certificate

example {Index : Type*}
    (active : Real -> Finset Index)
    (family : Index -> Real -> Real) (cost : Index -> Real)
    (costEnvelope : Real -> Real)
    (hfamilyNonneg : ∀ index coupling,
      0 <= family index coupling)
    (hfamilyBound : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        family index coupling <=
          weakCouplingLogarithmicFactor coupling * cost index)
    (hcostEnvelope : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      (∑ index ∈ active coupling, cost index) <= costEnvelope coupling)
    (hscaledEnvelope : Tendsto
      (fun coupling =>
        weakCouplingLogarithmicFactor coupling * costEnvelope coupling)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun coupling =>
        ∑ index ∈ active coupling, family index coupling)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growingFinset_sum_of_logCostEnvelope active family cost
    costEnvelope hfamilyNonneg hfamilyBound hcostEnvelope hscaledEnvelope

example {Index : Type*}
    (active : Real -> Finset Index)
    (family : Index -> Real -> Real) (cost : Index -> Real)
    (uniformCost : Real -> Real)
    (hfamilyNonneg : ∀ index coupling,
      0 <= family index coupling)
    (hfamilyBound : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        family index coupling <=
          weakCouplingLogarithmicFactor coupling * cost index)
    (huniformCost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling, cost index <= uniformCost coupling)
    (hscaledCardCost : Tendsto
      (fun coupling => weakCouplingLogarithmicFactor coupling *
        ((active coupling).card : Real) * uniformCost coupling)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun coupling =>
        ∑ index ∈ active coupling, family index coupling)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growingFinset_sum_of_card_mul_uniformCost active family cost
    uniformCost hfamilyNonneg hfamilyBound huniformCost hscaledCardCost

example {Index Omega : Type*}
    [MeasurableSpace Omega]
    (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (weight : Index -> Omega -> Complex)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ∀ index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index) (weight index) (observed index) (term index))
    (costEnvelope : Real -> Real)
    (hcostEnvelope : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      (∑ index ∈ active coupling,
        compactCertificateKineticCost (certificate index)) <=
          costEnvelope coupling)
    (hscaledEnvelope : Tendsto
      (fun coupling =>
        weakCouplingLogarithmicFactor coupling * costEnvelope coupling)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun coupling => ∑ index ∈ active coupling,
        weakCouplingKineticAccumulation
          (actualIteratedA2WeightedChannelExpectation ensemble
            (channel index) (weight index) (observed index) (term index))
          coupling)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growing_actualIteratedA2WeightedChannel_compact_of_costEnvelope
    active ensemble channel weight observed term certificate costEnvelope
      hcostEnvelope hscaledEnvelope

example {Index Omega : Type*}
    [MeasurableSpace Omega]
    (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (weight : Index -> Omega -> Complex)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ∀ index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index) (weight index) (observed index) (term index))
    (uniformCost : Real -> Real)
    (huniformCost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        compactCertificateKineticCost (certificate index) <=
          uniformCost coupling)
    (hscaledCardCost : Tendsto
      (fun coupling => weakCouplingLogarithmicFactor coupling *
        ((active coupling).card : Real) * uniformCost coupling)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun coupling => ∑ index ∈ active coupling,
        weakCouplingKineticAccumulation
          (actualIteratedA2WeightedChannelExpectation ensemble
            (channel index) (weight index) (observed index) (term index))
          coupling)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growing_actualIteratedA2WeightedChannel_compact_of_card_uniformCost
    active ensemble channel weight observed term certificate uniformCost
      huniformCost hscaledCardCost

end

end ArchonPhysicsConsumers.Thermalization
