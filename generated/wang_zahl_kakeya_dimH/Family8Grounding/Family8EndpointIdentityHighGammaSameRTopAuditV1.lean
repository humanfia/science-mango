import Family8Grounding.Family8EndpointIdentityHighGammaSameRBoundedCoreNativeThirdAutomaticDSOV1
import Family8Grounding.Family8NormalizedLongCoreThirdFirstCanonicalGraphRawEq66GammaNativeV1
import Family8Grounding.Family8Section8FixedPositiveSelfImprovementBudgetV3
import Mathlib.Tactic

/-!
# Audit of the top-level parameters for the same-R gamma-native route

The gamma-native third-first raw-Equation-(66) producer asks for the base
scale gain

`0 <= (1 - epsilon) * etaThird - 10 * eta stage / (epsilon * beta)`.

At the selected-true-split top interface, however, `etaThird` is at most
`eta 0`, and hence at most `eta stage`.  The parameter ladder makes
`epsilon * beta < 1`, so its displayed base exponent is strictly larger than
`eta stage`.  Thus the requested gain is strictly negative.  This is an
interface-direction obstruction, not a missing small-delta threshold.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8EndpointIdentityHighGammaSameRTopAuditV1

open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3

noncomputable section

/-- The `etaThird <= eta 0` supplied by the selected-true-split top callback
is incompatible with the base-scale gain demanded by the gamma-native
third-first raw-Equation-(66) producer. -/
theorem selectedTopThirdEta_not_thirdFirstRawEq66_baseScaleGain
    {epsilon0 beta gamma etaThird : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (stage : Nat) (hstage : stage <= P.N)
    (hetaThird : 0 < etaThird)
    (hetaThirdCap : etaThird <= P.eta 0) :
    ¬ 0 <=
      (1 - P.epsilon) * etaThird -
        (10 * P.eta stage / (P.epsilon * beta)) := by
  have hgapPos : 0 < gamma - beta :=
    P.epsilon_gap.trans' (mul_pos (by norm_num) P.epsilon_pos)
  have hbetaOne : beta < 1 := by linarith
  have hepsilonOne : P.epsilon < 1 := by
    have hgapOne : gamma - beta < 1 := by linarith
    nlinarith [P.epsilon_gap]
  have hdenomPos : 0 < P.epsilon * beta :=
    mul_pos P.epsilon_pos hbeta
  have hdenomOne : P.epsilon * beta < 1 := by
    nlinarith [P.epsilon_pos, hbeta]
  have hetaStage : P.eta 0 <= P.eta stage :=
    eta_zero_le_eta_of_stage_le P stage hstage
  have hetaPrimeLarge : P.eta stage <
      10 * P.eta stage / (P.epsilon * beta) := by
    apply (lt_div_iff₀ hdenomPos).2
    have hetaStagePos := P.eta_pos stage
    nlinarith
  have hcontract : (1 - P.epsilon) * etaThird < etaThird := by
    nlinarith [P.epsilon_pos]
  intro hgain
  have hchain : (1 - P.epsilon) * etaThird <
      10 * P.eta stage / (P.epsilon * beta) :=
    hcontract.trans_le (hetaThirdCap.trans hetaStage) |>.trans hetaPrimeLarge
  linarith

#print axioms selectedTopThirdEta_not_thirdFirstRawEq66_baseScaleGain

end
end Family8EndpointIdentityHighGammaSameRTopAuditV1
