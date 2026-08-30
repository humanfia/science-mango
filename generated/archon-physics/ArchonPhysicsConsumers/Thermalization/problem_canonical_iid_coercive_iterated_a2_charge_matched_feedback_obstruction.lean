import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackObstruction

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackObstruction
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open MeasureTheory

noncomputable section

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term)
    {g : Real} (hg : g ≠ 0) :
    actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble .total
        kappa radius observed term g =
      norm (∫ sample, actualIteratedA2StaticWeightSample ensemble kappa radius
        observed term sample ∂ensemble.probability) := by
  exact
    actualIteratedA2StaticExternalAccumulation_eq_feedbackNorm_of_chargeMatched
      ensemble kappa radius observed term hcharge hg

#print axioms actualIteratedA2TotalMismatchSample_eq_zero_of_chargeMatched
#print axioms actualIteratedA2WeightedTotalExpectation_eq_integral_of_chargeMatched
#print axioms weakCouplingKineticAccumulation_const
#print axioms actualIteratedA2StaticExternalAccumulation_eq_feedbackNorm_of_chargeMatched

end

end ArchonPhysicsConsumers.Thermalization
