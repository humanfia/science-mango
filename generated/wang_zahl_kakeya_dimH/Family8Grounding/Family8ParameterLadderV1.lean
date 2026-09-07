import Mathlib

namespace Family8ParameterLadderV1

set_option autoImplicit false
set_option warningAsError true

noncomputable section

/-!
# The quantitative parameter ladder in Main Lemma 1

The proof of the first self-improvement lemma chooses
`N >= 25 / epsilon0^2`, puts `epsilon = 1 / sqrt N`, and then chooses
`eta_0 <= ... <= eta_N` backwards.  This file makes those choices explicit.
In particular, the phrase "sufficiently small depending on the next eta" is
not retained as an assumption.
-/

/-- The paper's choice `epsilon = 1 / sqrt N`. -/
def reciprocalSqrt (N : Nat) : Real :=
  1 / Real.sqrt N

/-- A large integer simultaneously satisfies the sticky-theorem constraint
and leaves enough room in the exponent gap for the final estimate. -/
theorem exists_large_N
    {epsilon0 gap : Real} (hepsilon0 : 0 < epsilon0) (hgap : 0 < gap) :
    ∃ N : Nat,
      0 < N ∧
      25 / epsilon0 ^ 2 ≤ (N : Real) ∧
      0 < reciprocalSqrt N ∧
      reciprocalSqrt N ≤ epsilon0 / 5 ∧
      16 * reciprocalSqrt N < gap := by
  obtain ⟨N, hN⟩ :=
    exists_nat_gt
      (max (25 / epsilon0 ^ 2) ((16 / gap) ^ 2) : Real)
  have hNsticky : 25 / epsilon0 ^ 2 < (N : Real) :=
    (le_max_left _ _).trans_lt hN
  have hNgap : (16 / gap) ^ 2 < (N : Real) :=
    (le_max_right _ _).trans_lt hN
  have hNreal : 0 < (N : Real) :=
    (sq_nonneg (16 / gap)).trans_lt hNgap
  have hNnat : 0 < N := by exact_mod_cast hNreal
  have hsqrt : 0 < Real.sqrt (N : Real) := Real.sqrt_pos.2 hNreal
  have hepsilon : 0 < reciprocalSqrt N := by
    simp only [reciprocalSqrt]
    positivity
  have hrootGap : 16 / gap < Real.sqrt (N : Real) :=
    Real.lt_sqrt_of_sq_lt hNgap
  have hsixteen : 16 < gap * Real.sqrt (N : Real) := by
    have := (div_lt_iff₀ hgap).mp hrootGap
    nlinarith
  have hepsilonGap : 16 * reciprocalSqrt N < gap := by
    rw [reciprocalSqrt, mul_one_div]
    exact (div_lt_iff₀ hsqrt).2 hsixteen
  have hsqSticky : (5 / epsilon0) ^ 2 ≤ (N : Real) := by
    calc
      (5 / epsilon0) ^ 2 = 25 / epsilon0 ^ 2 := by ring
      _ ≤ (N : Real) := hNsticky.le
  have hrootSticky : 5 / epsilon0 ≤ Real.sqrt (N : Real) :=
    (Real.le_sqrt' (by positivity)).2 hsqSticky
  have hfive : 5 ≤ epsilon0 * Real.sqrt (N : Real) := by
    have := (div_le_iff₀ hepsilon0).mp hrootSticky
    nlinarith
  have hepsilonSticky : reciprocalSqrt N ≤ epsilon0 / 5 := by
    rw [reciprocalSqrt]
    apply (div_le_iff₀ hsqrt).2
    nlinarith
  exact ⟨N, hNnat, hNsticky.le, hepsilon, hepsilonSticky, hepsilonGap⟩

/-- The fixed contraction used when the `eta` parameters are chosen from
largest to smallest. -/
def ladderRatio (epsilon beta : Real) : Real :=
  min (1 / 2) (epsilon ^ 2 * beta / 20)

/-- A terminal value small enough for both exponent absorptions in the
paper's last two displays. -/
def ladderCap (epsilon beta gap : Real) : Real :=
  min (epsilon / 5) (epsilon * beta * gap / 400)

/-- An explicit version of the backwards choice
`eta_0 << eta_1 << ... << eta_N`. -/
def etaLadder (N j : Nat) (epsilon beta gap : Real) : Real :=
  ladderCap epsilon beta gap * ladderRatio epsilon beta ^ (N - j)

theorem ladderRatio_pos {epsilon beta : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) :
    0 < ladderRatio epsilon beta := by
  simp only [ladderRatio, lt_min_iff]
  constructor <;> positivity

theorem ladderRatio_le_one (epsilon beta : Real) :
    ladderRatio epsilon beta ≤ 1 := by
  exact (min_le_left _ _).trans (by norm_num)

theorem ladderRatio_le_scaled {epsilon beta : Real} :
    ladderRatio epsilon beta ≤ epsilon ^ 2 * beta / 20 :=
  min_le_right _ _

theorem ladderCap_pos {epsilon beta gap : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hgap : 0 < gap) :
    0 < ladderCap epsilon beta gap := by
  simp only [ladderCap, lt_min_iff]
  constructor <;> positivity

theorem etaLadder_pos {N j : Nat} {epsilon beta gap : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hgap : 0 < gap) :
    0 < etaLadder N j epsilon beta gap := by
  exact mul_pos (ladderCap_pos hepsilon hbeta hgap)
    (pow_pos (ladderRatio_pos hepsilon hbeta) _)

theorem etaLadder_le_epsilon_div_five
    {N j : Nat} {epsilon beta gap : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hgap : 0 < gap) :
    etaLadder N j epsilon beta gap ≤ epsilon / 5 := by
  have hratio0 : 0 ≤ ladderRatio epsilon beta :=
    (ladderRatio_pos hepsilon hbeta).le
  have hpow : ladderRatio epsilon beta ^ (N - j) ≤ 1 :=
    pow_le_one₀ hratio0 (ladderRatio_le_one epsilon beta)
  calc
    etaLadder N j epsilon beta gap
        ≤ ladderCap epsilon beta gap := by
          rw [etaLadder]
          exact mul_le_of_le_one_right
            (ladderCap_pos hepsilon hbeta hgap).le hpow
    _ ≤ epsilon / 5 := min_le_left _ _

theorem etaLadder_succ_relation
    {N j : Nat} {epsilon beta gap : Real} (hj : j < N) :
    etaLadder N j epsilon beta gap =
      ladderRatio epsilon beta * etaLadder N (j + 1) epsilon beta gap := by
  have hsub : N - j = (N - (j + 1)) + 1 := by omega
  rw [etaLadder, etaLadder, hsub, pow_succ]
  ring

theorem etaLadder_mono
    {N j : Nat} {epsilon beta gap : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hgap : 0 < gap)
    (hj : j < N) :
    etaLadder N j epsilon beta gap ≤
      etaLadder N (j + 1) epsilon beta gap := by
  rw [etaLadder_succ_relation hj]
  have hnext := etaLadder_pos (N := N) (j := j + 1) hepsilon hbeta hgap
  exact mul_le_of_le_one_left hnext.le (ladderRatio_le_one epsilon beta)

/-- This is the quantitative inequality used to force the intermediate
scale `b` below the dividing-scale threshold. -/
theorem etaPrime_le_epsilon_mul_next
    {N j : Nat} {epsilon beta gap : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hgap : 0 < gap)
    (hj : j < N) :
    10 * etaLadder N j epsilon beta gap / (epsilon * beta) ≤
      epsilon * etaLadder N (j + 1) epsilon beta gap := by
  rw [etaLadder_succ_relation hj]
  have hnext := etaLadder_pos (N := N) (j := j + 1) hepsilon hbeta hgap
  have hratio := ladderRatio_le_scaled (epsilon := epsilon) (beta := beta)
  have hdenom : 0 < epsilon * beta := mul_pos hepsilon hbeta
  apply (div_le_iff₀ hdenom).2
  have hten :
      10 * ladderRatio epsilon beta ≤ epsilon ^ 2 * beta := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hten hnext.le
  calc
    10 * (ladderRatio epsilon beta *
        etaLadder N (j + 1) epsilon beta gap) =
        (10 * ladderRatio epsilon beta) *
          etaLadder N (j + 1) epsilon beta gap := by ring
    _ ≤ (epsilon ^ 2 * beta) *
        etaLadder N (j + 1) epsilon beta gap := hmul
    _ = epsilon * etaLadder N (j + 1) epsilon beta gap *
        (epsilon * beta) := by ring

/-- Uniform control of the primed loss
`eta'_j = 10 eta_j / (epsilon beta)`. -/
theorem ten_etaPrime_le_half_gap
    {N j : Nat} {epsilon beta gap : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hgap : 0 < gap) :
    10 * (10 * etaLadder N j epsilon beta gap / (epsilon * beta)) ≤
      gap / 2 := by
  have hetaCap :
      etaLadder N j epsilon beta gap ≤ epsilon * beta * gap / 400 := by
    have hratio0 : 0 ≤ ladderRatio epsilon beta :=
      (ladderRatio_pos hepsilon hbeta).le
    have hpow : ladderRatio epsilon beta ^ (N - j) ≤ 1 :=
      pow_le_one₀ hratio0 (ladderRatio_le_one epsilon beta)
    calc
      etaLadder N j epsilon beta gap
          ≤ ladderCap epsilon beta gap := by
            rw [etaLadder]
            exact mul_le_of_le_one_right
              (ladderCap_pos hepsilon hbeta hgap).le hpow
      _ ≤ epsilon * beta * gap / 400 := min_le_right _ _
  have hdenom : 0 < epsilon * beta := mul_pos hepsilon hbeta
  rw [show 10 * (10 * etaLadder N j epsilon beta gap /
      (epsilon * beta)) =
      (100 * etaLadder N j epsilon beta gap) / (epsilon * beta) by ring]
  apply (div_le_iff₀ hdenom).2
  have hmul := mul_le_mul_of_nonneg_left hetaCap (by norm_num : (0 : Real) ≤ 100)
  calc
    100 * etaLadder N j epsilon beta gap ≤
        100 * (epsilon * beta * gap / 400) := hmul
    _ = (gap / 4) * (epsilon * beta) := by ring
    _ ≤ (gap / 2) * (epsilon * beta) :=
      mul_le_mul_of_nonneg_right (by linarith) hdenom.le

/-- The exact final exponent absorption used after generalized `K_KT`.
The stronger hypothesis `16 epsilon < gap` is supplied by `exists_large_N`. -/
theorem final_exponent_absorption
    {N j : Nat} {epsilon beta gap : Real}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hgap : 0 < gap)
    (hepsilonGap : 16 * epsilon < gap) :
    8 * epsilon +
        2 * (10 * etaLadder N j epsilon beta gap / (epsilon * beta)) < gap := by
  have hten := ten_etaPrime_le_half_gap
    (N := N) (j := j) hepsilon hbeta hgap
  have hetaPrime :
      2 * (10 * etaLadder N j epsilon beta gap / (epsilon * beta)) ≤ gap / 10 := by
    nlinarith
  nlinarith

/-- A single certificate collecting every numerical fact needed in the
long-interval branch of the self-improvement proof. -/
structure ParameterLadder (epsilon0 beta gamma : Real) where
  N : Nat
  epsilon : Real
  eta : Nat → Real
  N_pos : 0 < N
  epsilon_eq : epsilon = reciprocalSqrt N
  sticky_size : 25 / epsilon0 ^ 2 ≤ (N : Real)
  epsilon_pos : 0 < epsilon
  epsilon_le_sticky : epsilon ≤ epsilon0 / 5
  epsilon_gap : 16 * epsilon < gamma - beta
  eta_pos : ∀ j, 0 < eta j
  eta_le_epsilon_div_five : ∀ j, eta j ≤ epsilon / 5
  eta_mono : ∀ j, j < N → eta j ≤ eta (j + 1)
  etaPrime_le_next : ∀ j, j < N →
    10 * eta j / (epsilon * beta) ≤ epsilon * eta (j + 1)
  ten_etaPrime_le_half_gap : ∀ j,
    10 * (10 * eta j / (epsilon * beta)) ≤ (gamma - beta) / 2
  final_exponent_absorption : ∀ j,
    8 * epsilon + 2 * (10 * eta j / (epsilon * beta)) < gamma - beta

/-- The entire paper parameter ladder exists under precisely the positivity
conditions used by the proof. -/
theorem exists_parameterLadder
    {epsilon0 beta gamma : Real}
    (hepsilon0 : 0 < epsilon0) (hbeta : 0 < beta) (hbetagamma : beta < gamma) :
    Nonempty (ParameterLadder epsilon0 beta gamma) := by
  have hgap : 0 < gamma - beta := sub_pos.2 hbetagamma
  obtain ⟨N, hNpos, hNsticky, hepsilon, hepsilonSticky, hepsilonGap⟩ :=
    exists_large_N hepsilon0 hgap
  let epsilon := reciprocalSqrt N
  let eta : Nat → Real := fun j => etaLadder N j epsilon beta (gamma - beta)
  refine ⟨{
    N := N
    epsilon := epsilon
    eta := eta
    N_pos := hNpos
    epsilon_eq := rfl
    sticky_size := hNsticky
    epsilon_pos := hepsilon
    epsilon_le_sticky := hepsilonSticky
    epsilon_gap := hepsilonGap
    eta_pos := ?_
    eta_le_epsilon_div_five := ?_
    eta_mono := ?_
    etaPrime_le_next := ?_
    ten_etaPrime_le_half_gap := ?_
    final_exponent_absorption := ?_
  }⟩
  · intro j
    exact etaLadder_pos hepsilon hbeta hgap
  · intro j
    exact etaLadder_le_epsilon_div_five hepsilon hbeta hgap
  · intro j hj
    exact etaLadder_mono hepsilon hbeta hgap hj
  · intro j hj
    exact etaPrime_le_epsilon_mul_next hepsilon hbeta hgap hj
  · intro j
    exact ten_etaPrime_le_half_gap hepsilon hbeta hgap
  · intro j
    exact final_exponent_absorption hepsilon hbeta hgap hepsilonGap

#print axioms exists_large_N
#print axioms etaLadder_succ_relation
#print axioms etaPrime_le_epsilon_mul_next
#print axioms ten_etaPrime_le_half_gap
#print axioms final_exponent_absorption
#print axioms exists_parameterLadder

end

end Family8ParameterLadderV1
