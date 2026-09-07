import Family8Grounding.Family8ParameterLadderV1
import Mathlib.Tactic

/-!
# A parameter ladder with the high-gamma gate built into its terminal cap

This ADD-only module leaves the original `ParameterLadder` and its canonical
wiring untouched.  When `2 / 3 < gamma`, it replaces the terminal cap by

`min (ladderCap epsilon beta (gamma - beta))
  (epsilon ^ 2 * (3 * gamma - 2) / 20)`.

The contraction ratio is unchanged.  Consequently the resulting eta sequence
still has every field required by `ParameterLadder`, while every stage also
satisfies the strict high-gamma gate used by the existing singleton endpoint.
No DSO conclusion is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Family8HighGammaParameterLadderV1

open Family8ParameterLadderV1

noncomputable section

/-- The old terminal cap intersected with the strict high-gamma budget. -/
def highGammaLadderCap (epsilon beta gamma : Real) : Real :=
  min (ladderCap epsilon beta (gamma - beta))
    (epsilon ^ 2 * (3 * gamma - 2) / 20)

/-- The high-gamma ladder keeps the original contraction ratio. -/
def highGammaEtaLadder
    (N j : Nat) (epsilon beta gamma : Real) : Real :=
  highGammaLadderCap epsilon beta gamma *
    ladderRatio epsilon beta ^ (N - j)

theorem highGamma_gain_pos
    {gamma : Real} (hgamma : (2 : Real) / 3 < gamma) :
    0 < 3 * gamma - 2 := by
  linarith

theorem highGammaLadderCap_pos
    {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    0 < highGammaLadderCap epsilon beta gamma := by
  rw [highGammaLadderCap, lt_min_iff]
  exact ⟨ladderCap_pos hepsilon hbeta (sub_pos.mpr hbetagamma), by
    have hgain : 0 < 3 * gamma - 2 := highGamma_gain_pos hgamma
    positivity⟩

theorem highGammaLadderCap_le_oldCap
    (epsilon beta gamma : Real) :
    highGammaLadderCap epsilon beta gamma ≤
      ladderCap epsilon beta (gamma - beta) := by
  exact min_le_left _ _

theorem highGammaLadderCap_le_gainCap
    (epsilon beta gamma : Real) :
    highGammaLadderCap epsilon beta gamma ≤
      epsilon ^ 2 * (3 * gamma - 2) / 20 := by
  exact min_le_right _ _

theorem highGammaEtaLadder_pos
    {N j : Nat} {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    0 < highGammaEtaLadder N j epsilon beta gamma := by
  exact mul_pos
    (highGammaLadderCap_pos hepsilon hbeta hbetagamma hgamma)
    (pow_pos (ladderRatio_pos hepsilon hbeta) _)

theorem highGammaEtaLadder_le_oldCap
    {N j : Nat} {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    highGammaEtaLadder N j epsilon beta gamma ≤
      ladderCap epsilon beta (gamma - beta) := by
  have hratio0 : 0 ≤ ladderRatio epsilon beta :=
    (ladderRatio_pos hepsilon hbeta).le
  have hpow : ladderRatio epsilon beta ^ (N - j) ≤ 1 :=
    pow_le_one₀ hratio0 (ladderRatio_le_one epsilon beta)
  calc
    highGammaEtaLadder N j epsilon beta gamma ≤
        highGammaLadderCap epsilon beta gamma := by
      rw [highGammaEtaLadder]
      exact mul_le_of_le_one_right
        (highGammaLadderCap_pos hepsilon hbeta hbetagamma hgamma).le hpow
    _ ≤ ladderCap epsilon beta (gamma - beta) :=
      highGammaLadderCap_le_oldCap epsilon beta gamma

theorem highGammaEtaLadder_le_epsilon_div_five
    {N j : Nat} {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    highGammaEtaLadder N j epsilon beta gamma ≤ epsilon / 5 := by
  exact (highGammaEtaLadder_le_oldCap hepsilon hbeta hbetagamma hgamma).trans
    (min_le_left _ _)

theorem highGammaEtaLadder_succ_relation
    {N j : Nat} {epsilon beta gamma : Real} (hj : j < N) :
    highGammaEtaLadder N j epsilon beta gamma =
      ladderRatio epsilon beta *
        highGammaEtaLadder N (j + 1) epsilon beta gamma := by
  have hsub : N - j = (N - (j + 1)) + 1 := by omega
  rw [highGammaEtaLadder, highGammaEtaLadder, hsub, pow_succ]
  ring

theorem highGammaEtaLadder_mono
    {N j : Nat} {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma)
    (hj : j < N) :
    highGammaEtaLadder N j epsilon beta gamma ≤
      highGammaEtaLadder N (j + 1) epsilon beta gamma := by
  rw [highGammaEtaLadder_succ_relation hj]
  have hnext := highGammaEtaLadder_pos
    (N := N) (j := j + 1) hepsilon hbeta hbetagamma hgamma
  exact mul_le_of_le_one_left hnext.le
    (ladderRatio_le_one epsilon beta)

theorem highGammaEtaPrime_le_epsilon_mul_next
    {N j : Nat} {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma)
    (hj : j < N) :
    10 * highGammaEtaLadder N j epsilon beta gamma /
        (epsilon * beta) ≤
      epsilon * highGammaEtaLadder N (j + 1) epsilon beta gamma := by
  rw [highGammaEtaLadder_succ_relation hj]
  have hnext := highGammaEtaLadder_pos
    (N := N) (j := j + 1) hepsilon hbeta hbetagamma hgamma
  have hratio := ladderRatio_le_scaled
    (epsilon := epsilon) (beta := beta)
  have hdenom : 0 < epsilon * beta := mul_pos hepsilon hbeta
  apply (div_le_iff₀ hdenom).2
  have hten : 10 * ladderRatio epsilon beta ≤ epsilon ^ 2 * beta := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hten hnext.le
  calc
    10 * (ladderRatio epsilon beta *
        highGammaEtaLadder N (j + 1) epsilon beta gamma) =
        (10 * ladderRatio epsilon beta) *
          highGammaEtaLadder N (j + 1) epsilon beta gamma := by ring
    _ ≤ (epsilon ^ 2 * beta) *
        highGammaEtaLadder N (j + 1) epsilon beta gamma := hmul
    _ = epsilon * highGammaEtaLadder N (j + 1) epsilon beta gamma *
        (epsilon * beta) := by ring

theorem highGamma_ten_etaPrime_le_half_gap
    {N j : Nat} {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    10 * (10 * highGammaEtaLadder N j epsilon beta gamma /
        (epsilon * beta)) ≤ (gamma - beta) / 2 := by
  have hetaCap :
      highGammaEtaLadder N j epsilon beta gamma ≤
        epsilon * beta * (gamma - beta) / 400 :=
    (highGammaEtaLadder_le_oldCap hepsilon hbeta hbetagamma hgamma).trans
      (min_le_right _ _)
  have hdenom : 0 < epsilon * beta := mul_pos hepsilon hbeta
  rw [show 10 * (10 * highGammaEtaLadder N j epsilon beta gamma /
      (epsilon * beta)) =
      (100 * highGammaEtaLadder N j epsilon beta gamma) /
        (epsilon * beta) by ring]
  apply (div_le_iff₀ hdenom).2
  have hmul := mul_le_mul_of_nonneg_left hetaCap
    (by norm_num : (0 : Real) ≤ 100)
  calc
    100 * highGammaEtaLadder N j epsilon beta gamma ≤
        100 * (epsilon * beta * (gamma - beta) / 400) := hmul
    _ = ((gamma - beta) / 4) * (epsilon * beta) := by ring
    _ ≤ ((gamma - beta) / 2) * (epsilon * beta) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hdenom.le

theorem highGamma_final_exponent_absorption
    {N j : Nat} {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma)
    (hepsilonGap : 16 * epsilon < gamma - beta) :
    8 * epsilon +
        2 * (10 * highGammaEtaLadder N j epsilon beta gamma /
          (epsilon * beta)) < gamma - beta := by
  have hten := highGamma_ten_etaPrime_le_half_gap
    (N := N) (j := j) hepsilon hbeta hbetagamma hgamma
  have hetaPrime :
      2 * (10 * highGammaEtaLadder N j epsilon beta gamma /
        (epsilon * beta)) ≤ (gamma - beta) / 10 := by
    nlinarith
  nlinarith

/-- Every stage, including indices past `N`, satisfies the strict high-gamma
gate consumed by the singleton high-gamma endpoint. -/
theorem highGamma_ten_eta_lt_gain
    {N j : Nat} {epsilon beta gamma : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    10 * highGammaEtaLadder N j epsilon beta gamma <
      epsilon ^ 2 * (3 * gamma - 2) := by
  have hratio0 : 0 ≤ ladderRatio epsilon beta :=
    (ladderRatio_pos hepsilon hbeta).le
  have hpow : ladderRatio epsilon beta ^ (N - j) ≤ 1 :=
    pow_le_one₀ hratio0 (ladderRatio_le_one epsilon beta)
  have hcapPos :=
    highGammaLadderCap_pos hepsilon hbeta hbetagamma hgamma
  have hetaCap :
      highGammaEtaLadder N j epsilon beta gamma ≤
        highGammaLadderCap epsilon beta gamma := by
    rw [highGammaEtaLadder]
    exact mul_le_of_le_one_right hcapPos.le hpow
  have hetaGain :
      highGammaEtaLadder N j epsilon beta gamma ≤
        epsilon ^ 2 * (3 * gamma - 2) / 20 :=
    hetaCap.trans (highGammaLadderCap_le_gainCap epsilon beta gamma)
  have hgain : 0 < epsilon ^ 2 * (3 * gamma - 2) := by
    have := highGamma_gain_pos hgamma
    positivity
  nlinarith

theorem highGammaEtaLadder_terminal
    (N : Nat) (epsilon beta gamma : Real) :
    highGammaEtaLadder N N epsilon beta gamma =
      highGammaLadderCap epsilon beta gamma := by
  simp [highGammaEtaLadder]

/-- A standard `ParameterLadder` together with the explicit construction and
the additional strict gate.  The underlying ladder can be passed unchanged to
all pre-existing consumers. -/
structure HighGammaParameterLadder
    (epsilon0 beta gamma : Real) where
  ladder : ParameterLadder epsilon0 beta gamma
  gamma_gt_two_thirds : (2 : Real) / 3 < gamma
  eta_eq_highGammaEtaLadder : ∀ j,
    ladder.eta j = highGammaEtaLadder ladder.N j ladder.epsilon beta gamma
  terminal_eta_eq_cap :
    ladder.eta ladder.N =
      highGammaLadderCap ladder.epsilon beta gamma
  ten_eta_lt_gain : ∀ j,
    10 * ladder.eta j < ladder.epsilon ^ 2 * (3 * gamma - 2)

/-- Existence of the high-gamma ladder under the original positivity and gap
hypotheses plus the branch condition `2 / 3 < gamma`. -/
theorem exists_highGammaParameterLadder
    {epsilon0 beta gamma : Real}
    (hepsilon0 : 0 < epsilon0) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    Nonempty (HighGammaParameterLadder epsilon0 beta gamma) := by
  have hgap : 0 < gamma - beta := sub_pos.mpr hbetagamma
  obtain ⟨N, hNpos, hNsticky, hepsilon, hepsilonSticky, hepsilonGap⟩ :=
    exists_large_N hepsilon0 hgap
  let epsilon := reciprocalSqrt N
  let eta : Nat → Real := fun j =>
    highGammaEtaLadder N j epsilon beta gamma
  let P : ParameterLadder epsilon0 beta gamma := {
    N := N
    epsilon := epsilon
    eta := eta
    N_pos := hNpos
    epsilon_eq := rfl
    sticky_size := hNsticky
    epsilon_pos := hepsilon
    epsilon_le_sticky := hepsilonSticky
    epsilon_gap := hepsilonGap
    eta_pos := fun j =>
      highGammaEtaLadder_pos hepsilon hbeta hbetagamma hgamma
    eta_le_epsilon_div_five := fun j =>
      highGammaEtaLadder_le_epsilon_div_five
        hepsilon hbeta hbetagamma hgamma
    eta_mono := fun j hj =>
      highGammaEtaLadder_mono hepsilon hbeta hbetagamma hgamma hj
    etaPrime_le_next := fun j hj =>
      highGammaEtaPrime_le_epsilon_mul_next
        hepsilon hbeta hbetagamma hgamma hj
    ten_etaPrime_le_half_gap := fun j =>
      highGamma_ten_etaPrime_le_half_gap
        hepsilon hbeta hbetagamma hgamma
    final_exponent_absorption := fun j =>
      highGamma_final_exponent_absorption
        hepsilon hbeta hbetagamma hgamma hepsilonGap
  }
  refine ⟨{
    ladder := P
    gamma_gt_two_thirds := hgamma
    eta_eq_highGammaEtaLadder := ?_
    terminal_eta_eq_cap := ?_
    ten_eta_lt_gain := ?_
  }⟩
  · intro j
    rfl
  · exact highGammaEtaLadder_terminal N epsilon beta gamma
  · intro j
    exact highGamma_ten_eta_lt_gain
      hepsilon hbeta hbetagamma hgamma

/-- A choice of the complete high-gamma certificate. -/
noncomputable def canonicalHighGammaCertificate
    {epsilon0 beta gamma : Real}
    (hepsilon0 : 0 < epsilon0) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    HighGammaParameterLadder epsilon0 beta gamma :=
  Classical.choice
    (exists_highGammaParameterLadder hepsilon0 hbeta hbetagamma hgamma)

/-- The underlying standard ladder, ready for old endpoint wiring. -/
noncomputable def highGammaParameterLadder
    {epsilon0 beta gamma : Real}
    (hepsilon0 : 0 < epsilon0) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    ParameterLadder epsilon0 beta gamma :=
  (canonicalHighGammaCertificate
    hepsilon0 hbeta hbetagamma hgamma).ladder

theorem highGammaParameterLadder_ten_eta_lt_gain
    {epsilon0 beta gamma : Real}
    (hepsilon0 : 0 < epsilon0) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma)
    (stage : Nat) :
    let P := highGammaParameterLadder
      hepsilon0 hbeta hbetagamma hgamma
    10 * P.eta stage < P.epsilon ^ 2 * (3 * gamma - 2) := by
  dsimp only [highGammaParameterLadder]
  exact (canonicalHighGammaCertificate
    hepsilon0 hbeta hbetagamma hgamma).ten_eta_lt_gain stage

theorem highGammaParameterLadder_terminal_eta_eq_cap
    {epsilon0 beta gamma : Real}
    (hepsilon0 : 0 < epsilon0) (hbeta : 0 < beta)
    (hbetagamma : beta < gamma) (hgamma : (2 : Real) / 3 < gamma) :
    let P := highGammaParameterLadder
      hepsilon0 hbeta hbetagamma hgamma
    P.eta P.N = highGammaLadderCap P.epsilon beta gamma := by
  dsimp only [highGammaParameterLadder]
  exact (canonicalHighGammaCertificate
    hepsilon0 hbeta hbetagamma hgamma).terminal_eta_eq_cap

#print axioms highGammaEtaLadder_succ_relation
#print axioms highGammaEtaPrime_le_epsilon_mul_next
#print axioms highGamma_ten_eta_lt_gain
#print axioms exists_highGammaParameterLadder
#print axioms highGammaParameterLadder
#print axioms highGammaParameterLadder_ten_eta_lt_gain
#print axioms highGammaParameterLadder_terminal_eta_eq_cap

end

end Family8HighGammaParameterLadderV1
