import Family8Grounding.Family8CanonicalBufferedGlobalLongIntervalOuterAllocatedV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8IdentifiedDividingWitnessLongIntervalGainV1

open Submission.Kakeya.Uniformity
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

noncomputable section

/-!
# Convert the long-interval local gain to the global Section 8 gain

The literal equation-(66) endpoint has gain
`tau^(10 * (10 eta / (epsilon beta)))`.  The selected long interval gives
`tau <= delta^epsilon`; since `beta <= 1`, this is stronger than the single
global gain `delta^(10 eta)` used by the three-factor composition.
-/

namespace Witness

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

theorem tau_longIntervalGain_le_globalTenEta
    {fine : UniformTubeFamily delta index}
    (Cmulti : CoherentStickyMultiscaleCover fine)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : IdentifiedFrostmanDividingWitness
      fine Cmulti P.N P.epsilon P.eta Sseq)
    (hbeta : 0 < beta) (hbetaOne : beta <= 1) :
    (Sseq.tau W.m : ENNReal) ^
        (10 * (10 * P.eta W.stage / (P.epsilon * beta))) <=
      (delta : ENNReal) ^ (10 * P.eta W.stage) := by
  have hthetaOne : (Sseq.theta W.m : ENNReal) <= 1 := by
    exact_mod_cast Sseq.theta_le_one W.m
  have htauDelta : (Sseq.tau W.m : ENNReal) <=
      (delta : ENNReal) ^ P.epsilon := by
    calc
      (Sseq.tau W.m : ENNReal) <=
          (delta : ENNReal) ^ P.epsilon *
            (Sseq.theta W.m : ENNReal) := W.long
      _ <= (delta : ENNReal) ^ P.epsilon * 1 :=
        mul_le_mul' le_rfl hthetaOne
      _ = (delta : ENNReal) ^ P.epsilon := mul_one _
  have hlocalExponent :
      0 <= 10 * (10 * P.eta W.stage / (P.epsilon * beta)) := by
    have hquot : 0 <=
        10 * P.eta W.stage / (P.epsilon * beta) :=
      (div_pos (mul_pos (by norm_num) (P.eta_pos W.stage))
        (mul_pos P.epsilon_pos hbeta)).le
    positivity
  have hdeltaOneNN : delta <= 1 :=
    (Sseq.delta_le_tau W.m).trans
      ((Sseq.tau_le_theta W.m).trans (Sseq.theta_le_one W.m))
  have hdeltaOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast hdeltaOneNN
  have hbetaScale :
      10 * P.eta W.stage <= 100 * P.eta W.stage / beta := by
    have heta : 0 <= P.eta W.stage := (P.eta_pos W.stage).le
    have hten : 10 * P.eta W.stage <= 100 * P.eta W.stage := by
      nlinarith
    have hhundred :
        100 * P.eta W.stage <= 100 * P.eta W.stage / beta := by
      apply (le_div_iff₀ hbeta).2
      have hmul := mul_le_mul_of_nonneg_left hbetaOne
        (by positivity : 0 <= 100 * P.eta W.stage)
      simpa only [mul_one] using hmul
    exact hten.trans hhundred
  have hexponent :
      10 * P.eta W.stage <=
        P.epsilon *
          (10 * (10 * P.eta W.stage / (P.epsilon * beta))) := by
    calc
      10 * P.eta W.stage <= 100 * P.eta W.stage / beta := hbetaScale
      _ = P.epsilon *
          (10 * (10 * P.eta W.stage / (P.epsilon * beta))) := by
        field_simp [P.epsilon_pos.ne', hbeta.ne']
        ring
  calc
    (Sseq.tau W.m : ENNReal) ^
          (10 * (10 * P.eta W.stage / (P.epsilon * beta))) <=
        ((delta : ENNReal) ^ P.epsilon) ^
          (10 * (10 * P.eta W.stage / (P.epsilon * beta))) :=
      ENNReal.rpow_le_rpow htauDelta hlocalExponent
    _ = (delta : ENNReal) ^
          (P.epsilon *
            (10 * (10 * P.eta W.stage / (P.epsilon * beta)))) := by
      rw [← ENNReal.rpow_mul]
    _ <= (delta : ENNReal) ^ (10 * P.eta W.stage) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hdeltaOne hexponent

#print axioms tau_longIntervalGain_le_globalTenEta

end Witness
end
end Family8IdentifiedDividingWitnessLongIntervalGainV1
