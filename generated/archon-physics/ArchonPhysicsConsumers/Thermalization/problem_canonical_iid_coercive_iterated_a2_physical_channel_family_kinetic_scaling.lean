import ArchonPhysics.CanonicalIIDCoerciveIteratedA2PhysicalChannelFamilyKineticScaling

/-!
Consumer for fixed and external-`g`-dependent families of physical
iterated-A2 kinetic accumulations.  Each `kappa index` is fixed, while the
external variable `g` supplies exactly one weak-coupling square.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2PhysicalChannelFamilyKineticScaling
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

example {Index Omega : Type*} [MeasurableSpace Omega]
    (indices : Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (kappa : Index -> Real)
    (radius : Index -> Omega -> Lattice.Site N -> Real)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : forall index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index)
        (actualIteratedA2StaticWeightSample ensemble (kappa index) (radius index)
          (observed index) (term index))
        (observed index) (term index)) :
    Tendsto
      (fun g => ∑ index ∈ indices,
        actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          (channel index) (kappa index) (radius index) (observed index) (term index)
          g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_finset_actualIteratedA2StaticExternalWeakCouplingAccumulation_compact
    indices ensemble channel kappa radius observed term certificate

example {Index Omega : Type*} [MeasurableSpace Omega]
    (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (kappa : Index -> Real)
    (radius : Index -> Omega -> Lattice.Site N -> Real)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : forall index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index)
        (actualIteratedA2StaticWeightSample ensemble (kappa index) (radius index)
          (observed index) (term index))
        (observed index) (term index))
    (costEnvelope : Real -> Real)
    (hcostEnvelope : ∀ᶠ g in 𝓝[>] (0 : Real),
      (∑ index ∈ active g,
        compactCertificateKineticCost (certificate index)) <=
          costEnvelope g)
    (hscaledEnvelope : Tendsto
      (fun g =>
        weakCouplingLogarithmicFactor g * costEnvelope g)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          (channel index) (kappa index) (radius index) (observed index) (term index)
          g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growing_actualIteratedA2StaticExternalWeakCoupling_compact_of_costEnvelope
    active ensemble channel kappa radius observed term certificate costEnvelope
      hcostEnvelope hscaledEnvelope

example {Index Omega : Type*} [MeasurableSpace Omega]
    (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (kappa : Index -> Real)
    (radius : Index -> Omega -> Lattice.Site N -> Real)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : forall index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index)
        (actualIteratedA2StaticWeightSample ensemble (kappa index) (radius index)
          (observed index) (term index))
        (observed index) (term index))
    (uniformCost : Real -> Real)
    (huniformCost : ∀ᶠ g in 𝓝[>] (0 : Real),
      ∀ index ∈ active g,
        compactCertificateKineticCost (certificate index) <=
          uniformCost g)
    (hscaledCardCost : Tendsto
      (fun g => weakCouplingLogarithmicFactor g *
        ((active g).card : Real) * uniformCost g)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          (channel index) (kappa index) (radius index) (observed index) (term index)
          g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growing_actualIteratedA2StaticExternalWeakCoupling_compact_of_card_uniformCost
    active ensemble channel kappa radius observed term certificate uniformCost
      huniformCost hscaledCardCost

end

end ArchonPhysicsConsumers.Thermalization
