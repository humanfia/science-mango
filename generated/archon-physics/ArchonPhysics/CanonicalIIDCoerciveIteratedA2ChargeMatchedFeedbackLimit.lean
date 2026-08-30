import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackObstruction

/-!
# Weak-coupling limit of a charge-matched A2 feedback channel

The preceding exact identity says that every nonzero external coupling gives
the same kinetic-window accumulation for a charge-matched total channel.
This file records the corresponding punctured-neighbourhood limit and its
sharp non-decay consequence when the static feedback expectation is nonzero.
-/

namespace ArchonPhysics
namespace CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackLimit

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackObstruction
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- A charge-matched total channel converges to the norm of its static
feedback expectation, not to zero, on the standard `g^-2` window. -/
theorem tendsto_actualIteratedA2StaticExternalAccumulation_feedbackNorm_of_chargeMatched
    {Omega : Type*} [MeasurableSpace Omega]
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
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with g hg
  exact
    (actualIteratedA2StaticExternalAccumulation_eq_feedbackNorm_of_chargeMatched
      ensemble kappa radius observed term hcharge hg.ne').symm

/-- If the static feedback expectation is nonzero, the charge-matched total
channel cannot satisfy the Fourier-decay conclusion used for nonresonant
channels. -/
theorem not_tendsto_actualIteratedA2StaticExternalAccumulation_zero_of_chargeMatched
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term)
    (hfeedback : (∫ sample,
      actualIteratedA2StaticWeightSample ensemble kappa radius observed term
        sample ∂ensemble.probability) ≠ 0) :
    ¬ Tendsto
      (actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble .total
        kappa radius observed term)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  intro hzero
  have hlimit :=
    tendsto_actualIteratedA2StaticExternalAccumulation_feedbackNorm_of_chargeMatched
      ensemble kappa radius observed term hcharge
  have hneBot : NeBot (nhdsWithin (0 : Real) (Ioi 0)) :=
    nhdsWithin_Ioi_neBot le_rfl
  have heq :
      norm (∫ sample,
        actualIteratedA2StaticWeightSample ensemble kappa radius observed term
          sample ∂ensemble.probability) = 0 :=
    tendsto_nhds_unique hlimit hzero
  exact hfeedback (norm_eq_zero.mp heq)

end

end CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackLimit
end ArchonPhysics
