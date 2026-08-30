import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
import ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation

/-!
# External weak-coupling scaling for physical iterated-A2 channel families

In the standard alpha--beta normalization, each channel has a fixed base
coefficient `kappa index`.  The independent perturbative variable `g` supplies
the external factor `g ^ 2`, and the time window is `0 <= t <= g^-2`.

Every family transport uses the exact pointwise identity
`actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic`.  Thus the
physical accumulation is rewritten once as the abstract kinetic accumulation
of the fixed-`kappa` signal; no second `g ^ 2` factor is inserted.

The lattice size `N` remains fixed.  The active channel family may depend on
`g` only under an explicit aggregate certificate-cost condition.  These
statements do not control recollisions, higher Picard histories, or the full
Hamiltonian-to-kinetic limit.
-/

namespace
  ArchonPhysics.CanonicalIIDCoerciveIteratedA2PhysicalChannelFamilyKineticScaling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-! ## Fixed finite physical channel families -/

/-- A fixed finite sum of externally scaled physical A2 accumulations
vanishes when every fixed-`kappa` static weight has a compact mismatch
certificate.  The external scaling supplies exactly one factor `g ^ 2`. -/
theorem
    tendsto_finset_actualIteratedA2StaticExternalWeakCouplingAccumulation_compact
    {Index Omega : Type*} [MeasurableSpace Omega]
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
      (𝓝[>] 0) (𝓝 0) := by
  rw [show
    (fun g => ∑ index ∈ indices,
      actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        (channel index) (kappa index) (radius index) (observed index) (term index)
        g) =
      (fun g => ∑ index ∈ indices,
        weakCouplingKineticAccumulation
          (actualIteratedA2StaticWeightedChannelExpectation ensemble
            (channel index) (kappa index) (radius index) (observed index) (term index))
          g) by
    funext g
    apply Finset.sum_congr rfl
    intro index _hindex
    exact actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
      ensemble (channel index) (kappa index) (radius index) (observed index) (term index)
        g]
  exact
    tendsto_finset_actualIteratedA2WeightedChannel_compact_kineticAccumulation
      indices ensemble channel
      (fun index => actualIteratedA2StaticWeightSample ensemble (kappa index)
        (radius index) (observed index) (term index))
      observed term certificate

/-! ## External-`g`-dependent physical channel families -/

/-- An external-`g`-dependent finite family of physical A2 accumulations
vanishes when the logarithmic kinetic factor times an envelope for the total
fixed-`kappa` compact-certificate cost tends to zero. -/
theorem
    tendsto_growing_actualIteratedA2StaticExternalWeakCoupling_compact_of_costEnvelope
    {Index Omega : Type*} [MeasurableSpace Omega]
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
      (𝓝[>] 0) (𝓝 0) := by
  rw [show
    (fun g => ∑ index ∈ active g,
      actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        (channel index) (kappa index) (radius index) (observed index) (term index)
        g) =
      (fun g => ∑ index ∈ active g,
        weakCouplingKineticAccumulation
          (actualIteratedA2StaticWeightedChannelExpectation ensemble
            (channel index) (kappa index) (radius index) (observed index) (term index))
          g) by
    funext g
    apply Finset.sum_congr rfl
    intro index _hindex
    exact actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
      ensemble (channel index) (kappa index) (radius index) (observed index) (term index)
        g]
  exact
    tendsto_growing_actualIteratedA2WeightedChannel_compact_of_costEnvelope
      active ensemble channel
      (fun index => actualIteratedA2StaticWeightSample ensemble (kappa index)
        (radius index) (observed index) (term index))
      observed term certificate costEnvelope hcostEnvelope hscaledEnvelope

/-- Count-times-uniform-cost form of the growing physical-family criterion.
It makes the channel-growth requirement explicit while keeping `N` fixed. -/
theorem
    tendsto_growing_actualIteratedA2StaticExternalWeakCoupling_compact_of_card_uniformCost
    {Index Omega : Type*} [MeasurableSpace Omega]
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
      (𝓝[>] 0) (𝓝 0) := by
  rw [show
    (fun g => ∑ index ∈ active g,
      actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        (channel index) (kappa index) (radius index) (observed index) (term index)
        g) =
      (fun g => ∑ index ∈ active g,
        weakCouplingKineticAccumulation
          (actualIteratedA2StaticWeightedChannelExpectation ensemble
            (channel index) (kappa index) (radius index) (observed index) (term index))
          g) by
    funext g
    apply Finset.sum_congr rfl
    intro index _hindex
    exact actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic
      ensemble (channel index) (kappa index) (radius index) (observed index) (term index)
        g]
  exact
    tendsto_growing_actualIteratedA2WeightedChannel_compact_of_card_uniformCost
      active ensemble channel
      (fun index => actualIteratedA2StaticWeightSample ensemble (kappa index)
        (radius index) (observed index) (term index))
      observed term certificate uniformCost huniformCost hscaledCardCost

end

end
  ArchonPhysics.CanonicalIIDCoerciveIteratedA2PhysicalChannelFamilyKineticScaling
