import Family8Grounding.Family8Family7FirstCrossingExactOuterIdentitySingletonMiddleV6
import Family8Grounding.Family8HighGammaParameterLadderV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
import Mathlib.Tactic

/-!
# High-gamma power payment for the loss-free singleton middle

The endpoint identity ratio pays the complete middle coefficient
`sourceLoss * 4`.  The available exponent is chosen as half of the strict
high-gamma reserve supplied by `HighGammaParameterLadder`; no graph-bucket
loss or geometric proxy occurs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityHighGammaSameGraphLossFourPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Family7FirstCrossingExactOuterIdentitySingletonMiddleV6
open Family8FullRefinementActualDatumV1
open Family8HighGammaParameterLadderV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveRatioPowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Half of the strict high-gamma reserve is enough to pay the complete
loss-free singleton middle coefficient. -/
def sameGraphHighGammaMiddleLossExponent
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (stage : Nat) : Real :=
  (H.ladder.epsilon ^ 2 * (3 * gamma - 2) -
    10 * H.ladder.eta stage) / 2

theorem sameGraphHighGammaMiddleLossExponent_pos
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (stage : Nat) :
    0 < sameGraphHighGammaMiddleLossExponent H stage := by
  unfold sameGraphHighGammaMiddleLossExponent
  linarith [H.ten_eta_lt_gain stage]

/-- The endpoint ratio converts one power bound for `sourceLoss * 4` into
the exact middle field of `LongCoreThreeScaleDSOData`. -/
theorem endpointIdentity_highGamma_sourceLossFour_le_middle
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      H.ladder.N H.ladder.epsilon H.ladder.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hGammaOne : gamma <= 1)
    (sourceLoss : ENNReal)
    (houter : sourceLoss * 4 <=
      (delta : ENNReal) ^
        (-sameGraphHighGammaMiddleLossExponent H W.stage)) :
    sourceLoss * 4 <=
      (delta : ENNReal) ^ (10 * H.ladder.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          ((endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))).tau W.m)
          (canonicalBufferedRadius W) 1 gamma := by
  let P := H.ladder
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  have hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hgammaTwo : gamma <= 2 := hGammaOne.trans (by norm_num)
  obtain ⟨_q0, _qTop, hqPower⟩ :=
    canonicalBufferedTauActive_ratio_power_inputs E hE C S P W
  have hratio : (S.tau W.m : ENNReal) / (rho : ENNReal) <=
      (delta : ENNReal) ^ (P.epsilon ^ 2) := by
    simpa only [rho, ENNReal.coe_div hrho.ne'] using hqPower
  have hgain : 0 < 3 * gamma - 2 := by
    have hepsilonSq : 0 < P.epsilon ^ 2 := sq_pos_of_pos P.epsilon_pos
    have heta : 0 < 10 * P.eta W.stage := mul_pos (by norm_num) (P.eta_pos W.stage)
    have hstrict := H.ten_eta_lt_gain W.stage
    nlinarith
  have hbudget :
      10 * P.eta W.stage +
          sameGraphHighGammaMiddleLossExponent H W.stage <=
        P.epsilon ^ 2 * (3 * gamma - 2) := by
    unfold sameGraphHighGammaMiddleLossExponent
    dsimp only [P]
    linarith [H.ten_eta_lt_gain W.stage]
  simpa only [P, S, rho] using
    (sourceLoss_four_le_globalPower_mul_sectionEight_singleton
      hD.delta_pos hdeltaOne htau hrho hgammaTwo hgain hratio houter hbudget)

#print axioms sameGraphHighGammaMiddleLossExponent_pos
#print axioms endpointIdentity_highGamma_sourceLossFour_le_middle

end
end Family8EndpointIdentityHighGammaSameGraphLossFourPowerV1
