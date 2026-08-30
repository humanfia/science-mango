import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackLimit

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackLimit
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) :
    Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble .total
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0))
      (nhds (norm (∫ sample,
        actualIteratedA2StaticWeightSample ensemble kappa radius observed term
          sample ∂ensemble.probability))) := by
  exact
    tendsto_actualIteratedA2StaticExternalAccumulation_feedbackNorm_of_chargeMatched
      ensemble kappa radius observed term hcharge

#print axioms tendsto_actualIteratedA2StaticExternalAccumulation_feedbackNorm_of_chargeMatched
#print axioms not_tendsto_actualIteratedA2StaticExternalAccumulation_zero_of_chargeMatched

end

end ArchonPhysicsConsumers.Thermalization
