import ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling

/-! Consumer for actual fixed-volume A2 scaling from an L1 density. -/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2QualitativeL1Scaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open Filter MeasureTheory Set

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : ActualIteratedA2StaticL1FourierCertificate
      ensemble channel kappa radius observed term) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble channel
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualIteratedA2StaticExternalWeakCoupling_qualitativeL1
    ensemble channel kappa radius observed term certificate

#print axioms tendsto_actualIteratedA2WeightedChannel_qualitativeL1
#print axioms
  tendsto_actualIteratedA2StaticExternalWeakCoupling_qualitativeL1

end ArchonPhysicsConsumers.Thermalization
