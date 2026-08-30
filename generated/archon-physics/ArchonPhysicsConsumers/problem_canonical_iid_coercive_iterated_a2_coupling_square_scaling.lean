import ArchonPhysics.CanonicalIIDCoerciveIteratedA2CouplingSquareScaling

namespace ArchonPhysicsConsumers

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2CouplingSquareScaling
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

example
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (kappa : Real) (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (time : Real) :
    actualIteratedA2StaticWeightedChannelExpectation ensemble channel kappa
        radius observed term time =
      ((kappa : Complex) ^ 2) *
        actualIteratedA2StaticWeightedChannelExpectation ensemble channel 1
          radius observed term time := by
  exact
    actualIteratedA2StaticWeightedChannelExpectation_eq_coupling_sq_mul_unit
      ensemble channel kappa radius observed term time

end

end ArchonPhysicsConsumers
