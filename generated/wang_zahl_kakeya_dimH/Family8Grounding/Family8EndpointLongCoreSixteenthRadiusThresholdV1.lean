import Family8Grounding.Family8EndpointLongCoreHalfRadiusThresholdV2

/-!
# Automatic one-sixteenth radius bound for the endpoint long core

The one-step endpoint sequence has lower endpoint `delta` and upper endpoint
one.  Thus its canonical buffered radius is bounded by
`delta ^ (1 - epsilon)`.  Pulling `1/16` back through that positive power
packages the exact small-radius premise used by the same-assembly middle and
third-factor producers.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreSixteenthRadiusThresholdV1

open Submission.Kakeya.Uniformity
open Family8CanonicalBufferedGlobalFirstFactorEndpointV1
open Family8CanonicalLowerBufferedScaleV4
open Family8EndpointIdentityCoreSelectorV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {C : CoherentStickyMultiscaleCover fine}
  {epsilon0 beta gamma : Real}

/-- Positive endpoint threshold forcing every canonical buffered radius below
one sixteenth. -/
def endpointLongCoreSixteenthRadiusThreshold
    (P : ParameterLadder epsilon0 beta gamma) : NNReal :=
  positivePowerPullbackThreshold (1 - P.epsilon) (1 / 16 : NNReal)

theorem endpointLongCoreSixteenthRadiusThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1) :
    0 < endpointLongCoreSixteenthRadiusThreshold P := by
  apply positivePowerPullbackThreshold_pos
  · have hepsilonLt : P.epsilon < 1 :=
      parameterLadder_epsilon_lt_one P hbeta hgamma
    linarith
  · norm_num

/-- Literal `1/16` bound on the same endpoint witness used downstream. -/
theorem canonicalBufferedRadius_le_sixteenth_of_endpointSmall
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hdeltaOne : delta <= 1)
    (W : NormalizedLongIntervalCoreWitness
      fine C P.N P.epsilon P.eta
        (endpointScaleSequence delta hdeltaOne))
    (hsmall : delta <= endpointLongCoreSixteenthRadiusThreshold P) :
    canonicalBufferedRadius W <= (1 / 16 : NNReal) := by
  have hepsilonLt : P.epsilon < 1 :=
    parameterLadder_epsilon_lt_one P hbeta hgamma
  have hpowerPos : 0 < 1 - P.epsilon := by linarith
  have hdeltaPower : delta ^ (1 - P.epsilon) <= (1 / 16 : NNReal) :=
    rpow_le_target_of_le_positivePowerPullbackThreshold hpowerPos hsmall
  calc
    canonicalBufferedRadius W <=
        ((endpointScaleSequence delta hdeltaOne).tau W.m) ^
          (1 - P.epsilon) :=
      canonicalLowerBufferedScale_le_tau_rpow_one_sub
        ((endpointScaleSequence delta hdeltaOne).theta_le_one W.m)
        P.epsilon_pos.le
    _ = delta ^ (1 - P.epsilon) := by
      rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
        endpointScaleSequence_tau_zero]
    _ <= (1 / 16 : NNReal) := hdeltaPower

#print axioms endpointLongCoreSixteenthRadiusThreshold_pos
#print axioms canonicalBufferedRadius_le_sixteenth_of_endpointSmall

end
end Family8EndpointLongCoreSixteenthRadiusThresholdV1
