import ArchonPhysics.CanonicalIIDCoerciveIteratedA2PhysicalKineticScaling

namespace ArchonPhysicsConsumers

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2PhysicalKineticScaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeightedMismatchFiniteChartKineticClosure
open Filter
open scoped Topology

noncomputable section

example
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (certificate : ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel
        (actualIteratedA2StaticWeightSample ensemble 1 radius observed term)
        observed term ChartIndex) :
    Tendsto
      (actualIteratedA2StaticPhysicalKineticAccumulation ensemble channel
        radius observed term) (𝓝[>] 0) (𝓝 0) := by
  exact
    tendsto_actualIteratedA2StaticPhysicalKineticAccumulation_finiteChart
      ensemble channel radius observed term ChartIndex certificate

end

end ArchonPhysicsConsumers
