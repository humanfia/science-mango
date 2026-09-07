import Family8Grounding.Family8ParameterLadderV1

open scoped NNReal

namespace Family8LongIntervalBootstrapNumericsV1

open Family8ParameterLadderV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# The long-interval numerical bootstrap in Main Lemma 1

Put `X = b² |T_b|`, `A = 4 epsilon + etaPrime`, and
`q = gamma / 2 + beta - 1`.  The generalized Katz--Tao estimate factors as

`d⁻ᴬ X^q b^(2 (gamma-beta)) * b^(-2 gamma) X^(1-gamma/2)`.

The displayed `+ 2 (gamma-beta)` in the paper does **not** follow by replacing
`b` with `d`: the actual scale ordering is `d ≤ b`.  What makes the display
valid is the other actual scale relation `b ≤ d^(1-epsilon)`, together with
the exponent saved by using the two-sided bounds on `X` sharply.  The proof
below keeps that saving and treats the two possible signs of `q` separately.
-/

/-- The loss occurring in the maximal-concentration estimate. -/
def longIntervalDeltaLoss (epsilon etaPrime : Real) : Real :=
  4 * epsilon + etaPrime

/-- The exponent of `X = b² |T_b|` inside the Katz--Tao bracket. -/
def longIntervalXExponent (beta gamma : Real) : Real :=
  gamma / 2 + beta - 1

/-- The exponent in the paper's display immediately after the two-sided
estimate for `X`. -/
def longIntervalPaperExponent
    (epsilon etaPrime beta gamma : Real) : Real :=
  -2 * longIntervalDeltaLoss epsilon etaPrime + 2 * (gamma - beta)

theorem longIntervalPaperExponent_eq
    (epsilon etaPrime beta gamma : Real) :
    longIntervalPaperExponent epsilon etaPrime beta gamma =
      -8 * epsilon - 2 * etaPrime + 2 * (gamma - beta) := by
  simp only [longIntervalPaperExponent, longIntervalDeltaLoss]
  ring

/-- The first bracket after rewriting the Katz--Tao right-hand side in the
Frostman normalization. -/
def longIntervalKatzTaoBracket
    (d b X : NNReal) (epsilon etaPrime beta gamma : Real) : NNReal :=
  d ^ (-longIntervalDeltaLoss epsilon etaPrime) *
    X ^ longIntervalXExponent beta gamma *
      b ^ (2 * (gamma - beta))

/-- The normalized Katz--Tao expression before extracting the bracket. -/
def longIntervalKatzTaoRHS
    (d b X : NNReal) (epsilon etaPrime beta : Real) : NNReal :=
  d ^ (-longIntervalDeltaLoss epsilon etaPrime) *
    X ^ beta * b ^ (-2 * beta)

/-- The Frostman target in equation `multTildeTb`. -/
def longIntervalFrostmanTarget
    (d b X : NNReal) (etaPrime gamma : Real) : NNReal :=
  d ^ (10 * etaPrime) *
    b ^ (-2 * gamma) * X ^ (1 - gamma / 2)

theorem longIntervalXExponent_ge_neg_one
    {beta gamma : Real} (hbeta : 0 ≤ beta) (hbetaGamma : beta ≤ gamma) :
    -1 ≤ longIntervalXExponent beta gamma := by
  have hgamma : 0 ≤ gamma := hbeta.trans hbetaGamma
  simp only [longIntervalXExponent]
  linarith

theorem longIntervalXExponent_le_half
    {beta gamma : Real} (hbetaGamma : beta ≤ gamma) (hgamma : gamma ≤ 1) :
    longIntervalXExponent beta gamma ≤ 1 / 2 := by
  simp only [longIntervalXExponent]
  linarith

theorem longIntervalGap_mem_Icc
    {beta gamma : Real} (hbeta : 0 ≤ beta)
    (hbetaGamma : beta ≤ gamma) (hgamma : gamma ≤ 1) :
    0 ≤ gamma - beta ∧ gamma - beta ≤ 1 := by
  constructor <;> linarith

/-- In the nonnegative-`q` branch, the upper bound for `X` saves enough
exponent to pay for replacing `b` by `d^(1-epsilon)`. -/
theorem nonnegativeXExponent_budget
    {epsilon etaPrime beta gamma : Real}
    (hepsilon : 0 ≤ epsilon) (hetaPrime : 0 ≤ etaPrime)
    (hbeta : 0 ≤ beta) (hbetaGamma : beta ≤ gamma)
    (hgamma : gamma ≤ 1)
    (_hq : 0 ≤ longIntervalXExponent beta gamma) :
    longIntervalPaperExponent epsilon etaPrime beta gamma ≤
      -longIntervalDeltaLoss epsilon etaPrime +
          (-longIntervalDeltaLoss epsilon etaPrime) *
            longIntervalXExponent beta gamma +
        (1 - epsilon) * (2 * (gamma - beta)) := by
  have hqHalf := longIntervalXExponent_le_half hbetaGamma hgamma
  have hgap := longIntervalGap_mem_Icc hbeta hbetaGamma hgamma
  have hA : 4 * epsilon ≤ longIntervalDeltaLoss epsilon etaPrime := by
    simp only [longIntervalDeltaLoss]
    linarith
  have honeMinusQ : (1 / 2 : Real) ≤
      1 - longIntervalXExponent beta gamma := by
    linarith
  have hproduct :
      (4 * epsilon) * (1 / 2 : Real) ≤
        longIntervalDeltaLoss epsilon etaPrime *
          (1 - longIntervalXExponent beta gamma) := by
    exact mul_le_mul hA honeMinusQ (by positivity) (by linarith)
  have hgapCost :
      2 * epsilon * (gamma - beta) ≤ 2 * epsilon := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hgap.2
        (show 0 ≤ 2 * epsilon by positivity))
  simp only [longIntervalPaperExponent]
  nlinarith

/-- In the negative-`q` branch, the lower bound for `X` gives an even larger
exponent saving. -/
theorem negativeXExponent_budget
    {epsilon etaPrime beta gamma : Real}
    (hepsilon : 0 ≤ epsilon) (hetaPrime : 0 ≤ etaPrime)
    (hbeta : 0 ≤ beta) (hbetaGamma : beta ≤ gamma)
    (hgamma : gamma ≤ 1)
    (_hq : longIntervalXExponent beta gamma < 0) :
    longIntervalPaperExponent epsilon etaPrime beta gamma ≤
      -longIntervalDeltaLoss epsilon etaPrime +
          etaPrime * longIntervalXExponent beta gamma +
        (1 - epsilon) * (2 * (gamma - beta)) := by
  have hqLower := longIntervalXExponent_ge_neg_one hbeta hbetaGamma
  have hgap := longIntervalGap_mem_Icc hbeta hbetaGamma hgamma
  have hetaSaving :
      0 ≤ etaPrime * (1 + longIntervalXExponent beta gamma) :=
    mul_nonneg hetaPrime (by linarith)
  have hepsilonSaving :
      0 ≤ 2 * epsilon * (2 - (gamma - beta)) :=
    mul_nonneg (by positivity) (by linarith)
  simp only [longIntervalPaperExponent, longIntervalDeltaLoss]
  nlinarith

/-- Sharp use of both sides of `d^etaPrime ≤ X ≤ d^(-4epsilon-etaPrime)`
and of the actual scale bound `b ≤ d^(1-epsilon)` proves the bracket in
the paper.  This is where the sign of `q` is split. -/
theorem longIntervalKatzTaoBracket_le_paperPower
    {d b X : NNReal} {epsilon etaPrime beta gamma : Real}
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hbUpper : b ≤ d ^ (1 - epsilon))
    (hXLower : d ^ etaPrime ≤ X)
    (hXUpper : X ≤ d ^ (-longIntervalDeltaLoss epsilon etaPrime))
    (hepsilon : 0 ≤ epsilon) (hetaPrime : 0 ≤ etaPrime)
    (hbeta : 0 ≤ beta) (hbetaGamma : beta ≤ gamma)
    (hgamma : gamma ≤ 1) :
    longIntervalKatzTaoBracket d b X epsilon etaPrime beta gamma ≤
      d ^ longIntervalPaperExponent epsilon etaPrime beta gamma := by
  let A := longIntervalDeltaLoss epsilon etaPrime
  let q := longIntervalXExponent beta gamma
  let gap := gamma - beta
  have hgap : 0 ≤ gap := by dsimp only [gap]; linarith
  have hbPower :
      b ^ (2 * gap) ≤ d ^ ((1 - epsilon) * (2 * gap)) := by
    calc
      b ^ (2 * gap) ≤ (d ^ (1 - epsilon)) ^ (2 * gap) :=
        NNReal.rpow_le_rpow hbUpper (by positivity)
      _ = d ^ ((1 - epsilon) * (2 * gap)) :=
        (NNReal.rpow_mul d (1 - epsilon) (2 * gap)).symm
  change d ^ (-A) * X ^ q * b ^ (2 * gap) ≤
    d ^ longIntervalPaperExponent epsilon etaPrime beta gamma
  by_cases hq : 0 ≤ q
  · have hXPower : X ^ q ≤ d ^ ((-A) * q) := by
      calc
        X ^ q ≤ (d ^ (-A)) ^ q := NNReal.rpow_le_rpow hXUpper hq
        _ = d ^ ((-A) * q) := (NNReal.rpow_mul d (-A) q).symm
    have hexponent :
        longIntervalPaperExponent epsilon etaPrime beta gamma ≤
          -A + (-A) * q + (1 - epsilon) * (2 * gap) := by
      exact nonnegativeXExponent_budget hepsilon hetaPrime hbeta
        hbetaGamma hgamma hq
    calc
      d ^ (-A) * X ^ q * b ^ (2 * gap) ≤
          d ^ (-A) * d ^ ((-A) * q) *
            d ^ ((1 - epsilon) * (2 * gap)) :=
        mul_le_mul' (mul_le_mul' le_rfl hXPower) hbPower
      _ = d ^ (-A + (-A) * q + (1 - epsilon) * (2 * gap)) := by
        rw [NNReal.rpow_add hd.ne', NNReal.rpow_add hd.ne']
      _ ≤ d ^ longIntervalPaperExponent epsilon etaPrime beta gamma :=
        NNReal.rpow_le_rpow_of_exponent_ge hd hdOne hexponent
  · have hqNeg : q < 0 := lt_of_not_ge hq
    have hXPower : X ^ q ≤ d ^ (etaPrime * q) := by
      calc
        X ^ q ≤ (d ^ etaPrime) ^ q :=
          NNReal.rpow_le_rpow_of_nonpos
            (NNReal.rpow_pos hd) hXLower hqNeg.le
        _ = d ^ (etaPrime * q) :=
          (NNReal.rpow_mul d etaPrime q).symm
    have hexponent :
        longIntervalPaperExponent epsilon etaPrime beta gamma ≤
          -A + etaPrime * q + (1 - epsilon) * (2 * gap) := by
      exact negativeXExponent_budget hepsilon hetaPrime hbeta
        hbetaGamma hgamma hqNeg
    calc
      d ^ (-A) * X ^ q * b ^ (2 * gap) ≤
          d ^ (-A) * d ^ (etaPrime * q) *
            d ^ ((1 - epsilon) * (2 * gap)) :=
        mul_le_mul' (mul_le_mul' le_rfl hXPower) hbPower
      _ = d ^ (-A + etaPrime * q + (1 - epsilon) * (2 * gap)) := by
        rw [NNReal.rpow_add hd.ne', NNReal.rpow_add hd.ne']
      _ ≤ d ^ longIntervalPaperExponent epsilon etaPrime beta gamma :=
        NNReal.rpow_le_rpow_of_exponent_ge hd hdOne hexponent

/-- The `+2(gamma-beta)` term originates in this exact algebraic
factorization: `b^(-2 beta) = b^(2(gamma-beta)) b^(-2 gamma)`. -/
theorem longIntervalKatzTaoRHS_factorization
    {d b X : NNReal} {epsilon etaPrime beta gamma : Real}
    (hb : 0 < b) (hX : 0 < X) :
    longIntervalKatzTaoRHS d b X epsilon etaPrime beta =
      longIntervalKatzTaoBracket d b X epsilon etaPrime beta gamma *
        b ^ (-2 * gamma) * X ^ (1 - gamma / 2) := by
  have hXPower :
      X ^ beta =
        X ^ longIntervalXExponent beta gamma * X ^ (1 - gamma / 2) := by
    rw [← NNReal.rpow_add hX.ne']
    simp only [longIntervalXExponent]
    congr 1
    ring
  have hbPower :
      b ^ (-2 * beta) =
        b ^ (2 * (gamma - beta)) * b ^ (-2 * gamma) := by
    rw [← NNReal.rpow_add hb.ne']
    congr 1
    ring
  simp only [longIntervalKatzTaoRHS, longIntervalKatzTaoBracket,
    hXPower, hbPower]
  ring

/-- The normalized expression is exactly the original Katz--Tao term
`d⁻ᴬ (X / b²)^beta`. -/
theorem longIntervalKatzTaoRHS_eq_divisionForm
    {d b X : NNReal} {epsilon etaPrime beta : Real} :
    longIntervalKatzTaoRHS d b X epsilon etaPrime beta =
      d ^ (-longIntervalDeltaLoss epsilon etaPrime) *
        (X / b ^ 2) ^ beta := by
  have hbPower :
      (b ^ 2) ^ beta = b ^ (2 * beta) := by
    exact (NNReal.rpow_natCast_mul b 2 beta).symm
  have hbNeg :
      b ^ (-2 * beta) = (b ^ (2 * beta))⁻¹ := by
    rw [show -2 * beta = -(2 * beta) by ring, NNReal.rpow_neg]
  unfold longIntervalKatzTaoRHS
  rw [NNReal.div_rpow, div_eq_mul_inv, hbPower, hbNeg]
  ring

/-- The actual lower scale ordering has the opposite monotonic direction
from the tempting but invalid replacement `b ≤ d`. -/
theorem actualScaleOrdering_power_direction
    {d b : NNReal} {beta gamma : Real}
    (hdb : d ≤ b) (hbetaGamma : beta ≤ gamma) :
    d ^ (2 * (gamma - beta)) ≤ b ^ (2 * (gamma - beta)) := by
  exact NNReal.rpow_le_rpow hdb (by positivity)

/-- The ladder inequalities absorb the paper exponent into the requested
`10 etaPrime` gain. -/
theorem parameterLadder_paperExponent_absorption
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hbeta : 0 < beta) :
    10 * (10 * P.eta j / (P.epsilon * beta)) ≤
      longIntervalPaperExponent P.epsilon
        (10 * P.eta j / (P.epsilon * beta)) beta gamma := by
  have hfinal := P.final_exponent_absorption j
  have hten := P.ten_etaPrime_le_half_gap j
  have hetaPrime :
      0 < 10 * P.eta j / (P.epsilon * beta) := by
    exact div_pos (mul_pos (by norm_num) (P.eta_pos j))
      (mul_pos P.epsilon_pos hbeta)
  have hgap : 0 < gamma - beta := by
    nlinarith [P.epsilon_pos]
  simp only [longIntervalPaperExponent, longIntervalDeltaLoss]
  nlinarith

/-- Full numerical implication from the normalized generalized Katz--Tao
right-hand side to the Frostman target, with the primed loss supplied by the
explicit parameter ladder. -/
theorem longIntervalKatzTaoRHS_le_frostmanTarget
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    {d b X : NNReal}
    (hd : 0 < d) (hdOne : d ≤ 1) (hdb : d ≤ b)
    (hbUpper : b ≤ d ^ (1 - P.epsilon))
    (hXLower : d ^ (10 * P.eta j / (P.epsilon * beta)) ≤ X)
    (hXUpper : X ≤ d ^
      (-longIntervalDeltaLoss P.epsilon
        (10 * P.eta j / (P.epsilon * beta))))
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1) :
    longIntervalKatzTaoRHS d b X P.epsilon
        (10 * P.eta j / (P.epsilon * beta)) beta ≤
      longIntervalFrostmanTarget d b X
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  let etaPrime := 10 * P.eta j / (P.epsilon * beta)
  have hb : 0 < b := hd.trans_le hdb
  have hetaPrime : 0 ≤ etaPrime := by
    dsimp only [etaPrime]
    exact div_nonneg (mul_nonneg (by norm_num) (P.eta_pos j).le)
      (mul_nonneg P.epsilon_pos.le hbeta.le)
  have hbetaGamma : beta ≤ gamma := by
    have := P.epsilon_gap
    nlinarith [P.epsilon_pos]
  have hbracket :
      longIntervalKatzTaoBracket d b X P.epsilon etaPrime beta gamma ≤
        d ^ longIntervalPaperExponent P.epsilon etaPrime beta gamma :=
    longIntervalKatzTaoBracket_le_paperPower hd hdOne hbUpper
      hXLower hXUpper P.epsilon_pos.le hetaPrime hbeta.le
      hbetaGamma hgamma
  have habsorb :
      d ^ longIntervalPaperExponent P.epsilon etaPrime beta gamma ≤
        d ^ (10 * etaPrime) := by
    apply NNReal.rpow_le_rpow_of_exponent_ge hd hdOne
    exact parameterLadder_paperExponent_absorption P j hbeta
  rw [longIntervalKatzTaoRHS_factorization hb
    (lt_of_lt_of_le (NNReal.rpow_pos hd) hXLower)]
  calc
    longIntervalKatzTaoBracket d b X P.epsilon etaPrime beta gamma *
          b ^ (-2 * gamma) * X ^ (1 - gamma / 2) ≤
        d ^ longIntervalPaperExponent P.epsilon etaPrime beta gamma *
          b ^ (-2 * gamma) * X ^ (1 - gamma / 2) := by
      exact mul_le_mul' (mul_le_mul' hbracket le_rfl) le_rfl
    _ ≤ d ^ (10 * etaPrime) *
          b ^ (-2 * gamma) * X ^ (1 - gamma / 2) := by
      exact mul_le_mul' (mul_le_mul' habsorb le_rfl) le_rfl
    _ = longIntervalFrostmanTarget d b X etaPrime gamma := rfl

/-! ## Lossless `ENNReal` front end -/

/-- The finite normalized Katz--Tao expression, written in the codomain used
by the multiplicity theorems. -/
def longIntervalKatzTaoRHSENNReal
    (d b X : NNReal) (epsilon etaPrime beta : Real) : ENNReal :=
  (d : ENNReal) ^ (-longIntervalDeltaLoss epsilon etaPrime) *
    (X : ENNReal) ^ beta * (b : ENNReal) ^ (-2 * beta)

/-- The finite Frostman target, written in `ENNReal`. -/
def longIntervalFrostmanTargetENNReal
    (d b X : NNReal) (etaPrime gamma : Real) : ENNReal :=
  (d : ENNReal) ^ (10 * etaPrime) *
    (b : ENNReal) ^ (-2 * gamma) *
      (X : ENNReal) ^ (1 - gamma / 2)

theorem coe_longIntervalKatzTaoRHS
    {d b X : NNReal} {epsilon etaPrime beta : Real}
    (hd : 0 < d) (hb : 0 < b) (hX : 0 < X) :
    (longIntervalKatzTaoRHS d b X epsilon etaPrime beta : ENNReal) =
      longIntervalKatzTaoRHSENNReal d b X epsilon etaPrime beta := by
  simp only [longIntervalKatzTaoRHS, longIntervalKatzTaoRHSENNReal,
    ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hd.ne',
    ENNReal.coe_rpow_of_ne_zero hb.ne',
    ENNReal.coe_rpow_of_ne_zero hX.ne']

theorem coe_longIntervalFrostmanTarget
    {d b X : NNReal} {etaPrime gamma : Real}
    (hd : 0 < d) (hb : 0 < b) (hX : 0 < X) :
    (longIntervalFrostmanTarget d b X etaPrime gamma : ENNReal) =
      longIntervalFrostmanTargetENNReal d b X etaPrime gamma := by
  simp only [longIntervalFrostmanTarget,
    longIntervalFrostmanTargetENNReal, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_ne_zero hd.ne',
    ENNReal.coe_rpow_of_ne_zero hb.ne',
    ENNReal.coe_rpow_of_ne_zero hX.ne']

/-- Direct multiplicity-facing form of the long-interval numerical
implication.  No `toNNReal` or finiteness premise is needed: the three
underlying quantities are already finite `NNReal` data. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    {d b X : NNReal}
    (hd : 0 < d) (hdOne : d ≤ 1) (hdb : d ≤ b)
    (hbUpper : b ≤ d ^ (1 - P.epsilon))
    (hXLower : d ^ (10 * P.eta j / (P.epsilon * beta)) ≤ X)
    (hXUpper : X ≤ d ^
      (-longIntervalDeltaLoss P.epsilon
        (10 * P.eta j / (P.epsilon * beta))))
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1) :
    longIntervalKatzTaoRHSENNReal d b X P.epsilon
        (10 * P.eta j / (P.epsilon * beta)) beta ≤
      longIntervalFrostmanTargetENNReal d b X
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  have hb : 0 < b := hd.trans_le hdb
  have hX : 0 < X :=
    lt_of_lt_of_le (NNReal.rpow_pos hd) hXLower
  have hcore := longIntervalKatzTaoRHS_le_frostmanTarget P j hd hdOne hdb
    hbUpper hXLower hXUpper hbeta hgamma
  rw [← coe_longIntervalKatzTaoRHS hd hb hX,
    ← coe_longIntervalFrostmanTarget hd hb hX]
  exact_mod_cast hcore

#print axioms longIntervalKatzTaoBracket_le_paperPower
#print axioms longIntervalKatzTaoRHS_factorization
#print axioms actualScaleOrdering_power_direction
#print axioms parameterLadder_paperExponent_absorption
#print axioms longIntervalKatzTaoRHS_le_frostmanTarget
#print axioms longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal

end

end Family8LongIntervalBootstrapNumericsV1
