import Family8Grounding.Family8CanonicalBufferedGlobalFirstFactorEndpointV1
import Family8Grounding.Family8EndpointIdentityCoreSelectorV2
import Family8Grounding.Family8NormalizedLongIntervalCoreConsumerV1
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import Mathlib.Tactic

/-!
# Automatic half-radius bound for the endpoint long core, V2

On the one-step endpoint sequence the selected interval has literal lower
endpoint `delta` and upper endpoint `1`.  Hence the canonical buffered radius
is at most `delta^(1-epsilon)`.  Pulling `1/2` back through this positive power
gives one explicit positive threshold which discharges the selected-Frostman
half-radius input at the final endpoint orchestration.

V1 attempted to case-split directly on a structure projection and is not
imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreHalfRadiusThresholdV2

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

/-- The positive small-delta threshold forcing the endpoint long-core
canonical radius below one half. -/
def endpointLongCoreHalfRadiusThreshold
    (P : ParameterLadder epsilon0 beta gamma) : NNReal :=
  positivePowerPullbackThreshold (1 - P.epsilon) (2 : NNReal)⁻¹

theorem endpointLongCoreHalfRadiusThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1) :
    0 < endpointLongCoreHalfRadiusThreshold P := by
  apply positivePowerPullbackThreshold_pos
  · have hepsilonLt : P.epsilon < 1 :=
      parameterLadder_epsilon_lt_one P hbeta hgamma
    linarith
  · norm_num

/-- Every long-core witness on the endpoint sequence automatically has
canonical buffered radius at most one half below the displayed threshold. -/
theorem canonicalBufferedRadius_le_half_of_endpointSmall
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1)
    (hdeltaOne : delta ≤ 1)
    (W : NormalizedLongIntervalCoreWitness
      fine C P.N P.epsilon P.eta
        (endpointScaleSequence delta hdeltaOne))
    (hsmall : delta ≤ endpointLongCoreHalfRadiusThreshold P) :
    canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹ := by
  have hepsilonLt : P.epsilon < 1 :=
    parameterLadder_epsilon_lt_one P hbeta hgamma
  have hpowerPos : 0 < 1 - P.epsilon := by linarith
  have hdeltaPower : delta ^ (1 - P.epsilon) ≤ (2 : NNReal)⁻¹ :=
    rpow_le_target_of_le_positivePowerPullbackThreshold hpowerPos hsmall
  calc
    canonicalBufferedRadius W ≤
        ((endpointScaleSequence delta hdeltaOne).tau W.m) ^
          (1 - P.epsilon) :=
      canonicalLowerBufferedScale_le_tau_rpow_one_sub
        ((endpointScaleSequence delta hdeltaOne).theta_le_one W.m)
        P.epsilon_pos.le
    _ = delta ^ (1 - P.epsilon) := by
      rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
        endpointScaleSequence_tau_zero]
    _ ≤ (2 : NNReal)⁻¹ := hdeltaPower

#print axioms endpointLongCoreHalfRadiusThreshold_pos
#print axioms canonicalBufferedRadius_le_half_of_endpointSmall

end

end Family8EndpointLongCoreHalfRadiusThresholdV2
