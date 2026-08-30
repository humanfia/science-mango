import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
import ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity

/-!
# Charge-matched A2 feedback is not an oscillatory error

For a return tree whose complete phase charge equals the free observed
charge, the outer and inner second-Picard mismatches cancel exactly.  Hence
the `.total` A2 channel has zero phase for every microscopic mass sample.

The resulting weighted expectation is constant in time.  On the standard
external weak-coupling window `T = g^-2`, its `g^2`-scaled positive-time
accumulation is therefore exactly the norm of its static expectation (for
`g != 0`), rather than a term tending to zero.  Such channels belong in the
resonant feedback block and must not be sent through a transversality or
Fourier-decay estimate.
-/

namespace ArchonPhysics
namespace CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackObstruction

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open MeasureTheory

noncomputable section

/-- A charge-matched actual total mismatch is identically zero, before any
averaging over the iid ensemble. -/
theorem actualIteratedA2TotalMismatchSample_eq_zero_of_chargeMatched
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) (sample : Omega) :
    actualIteratedA2MismatchSample ensemble .total observed term sample = 0 := by
  change iteratedQuadraticOuterMismatch
      (ensemble.restrictPositiveMass (N := N) sample) observed term +
    iteratedQuadraticInnerMismatch
      (ensemble.restrictPositiveMass (N := N) sample) term = 0
  rw [iteratedQuadraticOuterMismatch_eq_neg_inner_of_charge_eq_freeInitial
    _ observed term hcharge]
  ring

/-- With zero total mismatch, an arbitrary weighted A2 expectation is the
static integral of its weight and has no time oscillation. -/
theorem actualIteratedA2WeightedTotalExpectation_eq_integral_of_chargeMatched
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (weight : Omega -> Complex)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) (time : Real) :
    actualIteratedA2WeightedChannelExpectation ensemble .total weight observed
        term time =
      ∫ sample, weight sample ∂ensemble.probability := by
  unfold actualIteratedA2WeightedChannelExpectation
    weightedMismatchExpectation
  apply integral_congr_ae
  filter_upwards with sample
  rw [actualIteratedA2TotalMismatchSample_eq_zero_of_chargeMatched
    ensemble observed term hcharge sample]
  simp

/-- Static-coefficient specialization of the exact constant-signal identity. -/
theorem actualIteratedA2StaticWeightedTotalExpectation_eq_integral_of_chargeMatched
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (kappa : Real)
    (radius : Omega -> Lattice.Site N -> Real)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) (time : Real) :
    actualIteratedA2StaticWeightedChannelExpectation ensemble .total kappa
        radius observed term time =
      ∫ sample, actualIteratedA2StaticWeightSample ensemble kappa radius
        observed term sample ∂ensemble.probability := by
  exact actualIteratedA2WeightedTotalExpectation_eq_integral_of_chargeMatched
    ensemble
      (actualIteratedA2StaticWeightSample ensemble kappa radius observed term)
      observed term hcharge time

/-- A constant channel accumulates to exactly its norm on the kinetic window.
This elementary identity is the normalization behind the feedback
obstruction. -/
theorem weakCouplingKineticAccumulation_const
    (value : Complex) {g : Real} (hg : g ≠ 0) :
    weakCouplingKineticAccumulation (fun _time => value) g = norm value := by
  unfold weakCouplingKineticAccumulation weakCouplingKineticTime
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  have hsquare : g ^ 2 ≠ 0 := pow_ne_zero 2 hg
  rw [← mul_assoc, mul_inv_cancel₀ hsquare, one_mul]

/-- The charge-matched physical total channel is an exact `O(1)` feedback
contribution after external `g^2` scaling and integration to `g^-2`. -/
theorem actualIteratedA2StaticExternalAccumulation_eq_feedbackNorm_of_chargeMatched
    {Omega : Type*} [MeasurableSpace Omega]
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
  rw [actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic]
  have hsignal :
      actualIteratedA2StaticWeightedChannelExpectation ensemble .total kappa
          radius observed term =
        fun _time => ∫ sample,
          actualIteratedA2StaticWeightSample ensemble kappa radius observed term
            sample ∂ensemble.probability := by
    funext time
    exact
      actualIteratedA2StaticWeightedTotalExpectation_eq_integral_of_chargeMatched
        ensemble kappa radius observed term hcharge time
  rw [hsignal]
  exact weakCouplingKineticAccumulation_const _ hg

end

end CanonicalIIDCoerciveIteratedA2ChargeMatchedFeedbackObstruction
end ArchonPhysics
