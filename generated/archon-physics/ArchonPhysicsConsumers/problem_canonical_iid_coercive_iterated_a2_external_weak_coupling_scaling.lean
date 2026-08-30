import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling

namespace ArchonPhysicsConsumers

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter
open scoped Topology

noncomputable section

example
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2WeightedChannelCompactIntervalCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
        observed term) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term) (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_actualIteratedA2StaticExternalWeakCouplingAccumulation_compact
    ensemble channel kappa radius observed term certificate

end

end ArchonPhysicsConsumers
