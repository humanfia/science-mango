import Family8Grounding.Family8PaperFactorFiniteRunV1
import Family8Grounding.Family8PaperFactorFiniteRunV2
import Family8Grounding.Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Power envelopes for a finite paper-factor run

The finite paper-factor run records the literal losses `C_j` and `L_j` of
every genuine bad-parent transition.  Finiteness of the run alone does not
bound those arbitrary `ENNReal` values by a power of the source scale (in
particular the transition type does not require `C_j != infinity`).

This file isolates the earliest honest analytic seam in two complementary
forms.

* `RepeatedBadParentLocalExponentBudget` gives pointwise power bounds for the
  actual displayed `C_j` and `L_j`.  Their products are proved to cost exactly
  the sums of the displayed local exponents.
* `RepeatedBadParentFiniteLossData` asks only that the same displayed losses
  are finite.  The existing finite-constant small-scale theorem then gives an
  explicit positive threshold below which any prescribed positive forward
  and reverse exponents absorb the two finite products.

Neither route assumes either cumulative power envelope requested by the
correlated Equation (66) connector.
-/

/-! The finite-loss threshold is datum-local: it depends on the already chosen
run and therefore on its scale-dependent losses.  It is not advertised as a
uniform top-level `rawDelta0`.  The local-exponent route is the reusable
top-level seam. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace Family8PaperFactorFiniteRunPowerEnvelopeV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperFactorFiniteRunV1
open Family8PaperFactorFiniteRunV1.PaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1.RepeatedBadParentLedger
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-! ## Positivity and small-scale control retained by paper readiness -/

/-- Every literal factor radius in a paper readiness list is positive, so
their finite product is positive. -/
theorem factorRadiusProduct_pos_of_readiness
    {factors : List ActualFactorDatum}
    (readiness : PaperFactorReadinessList factors) :
    0 < factorRadiusProduct factors := by
  induction readiness with
  | nil => simp
  | @cons A tail head tailReadiness ih =>
      let _ : Fintype A.index := A.fintypeIndex
      let _ : DecidableEq A.index := A.decidableEqIndex
      simp only [factorRadiusProduct_cons]
      exact mul_pos head.admissible.delta_pos ih

/-- Admissibility bounds every literal factor radius by `1/2`, hence a
paper-ready finite product is at most one. -/
theorem factorRadiusProduct_le_one_of_readiness
    {factors : List ActualFactorDatum}
    (readiness : PaperFactorReadinessList factors) :
    factorRadiusProduct factors <= 1 := by
  induction readiness with
  | nil => simp
  | @cons A tail head tailReadiness ih =>
      let _ : Fintype A.index := A.fintypeIndex
      let _ : DecidableEq A.index := A.decidableEqIndex
      simp only [factorRadiusProduct_cons]
      calc
        A.radius * factorRadiusProduct tail <= 1 * 1 := by
          gcongr
          exact head.admissible.delta_le_half.trans (by norm_num)
        _ = 1 := by norm_num

/-! ## Generic pointwise-to-product power algebra -/

/-- Pointwise powers of one positive finite base multiply to the negative
power of the sum of their displayed costs. -/
theorem list_prod_le_rpow_neg_sum
    (base : NNReal) (hbase : 0 < base)
    (steps : List BadParentProductStep)
    (value : BadParentProductStep -> ENNReal)
    (exponent : BadParentProductStep -> Real)
    (hvalue : forall step, step ∈ steps ->
      value step <= (base : ENNReal) ^ (-exponent step)) :
    (steps.map value).prod <=
      (base : ENNReal) ^ (-(steps.map exponent).sum) := by
  induction steps with
  | nil => simp
  | cons step tail ih =>
      have hhead : value step <=
          (base : ENNReal) ^ (-exponent step) :=
        hvalue step (by simp)
      have htail : (tail.map value).prod <=
          (base : ENNReal) ^ (-(tail.map exponent).sum) :=
        ih (fun next hnext => hvalue next (by simp [hnext]))
      have hbase0 : (base : ENNReal) ≠ 0 :=
        ENNReal.coe_ne_zero.mpr hbase.ne'
      have hbaseTop : (base : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      calc
        value step * (tail.map value).prod <=
            (base : ENNReal) ^ (-exponent step) *
              (base : ENNReal) ^ (-(tail.map exponent).sum) :=
          mul_le_mul' hhead htail
        _ = (base : ENNReal) ^
              ((-exponent step) + (-(tail.map exponent).sum)) := by
          rw [ENNReal.rpow_add _ _ hbase0 hbaseTop]
        _ = (base : ENNReal) ^
              (-(exponent step + (tail.map exponent).sum)) := by
          congr 1
          ring

/-! ## Local exponent data on the actual scalar ledger -/

/-- Pointwise analytic power data for every actual step in one repeated
bad-parent ledger.  The hypotheses mention the literal stored losses, not a
cumulative product. -/
structure RepeatedBadParentLocalExponentBudget
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (base : NNReal) where
  uniformityExponent : BadParentProductStep -> Real
  freshRetentionExponent : BadParentProductStep -> Real
  uniformity_upper : forall step, step ∈ ledger.steps ->
    step.uniformityLoss <=
      (base : ENNReal) ^ (-uniformityExponent step)
  freshRetention_upper : forall step, step ∈ ledger.steps ->
    step.freshRetentionLoss <=
      (base : ENNReal) ^ (-freshRetentionExponent step)

namespace RepeatedBadParentLocalExponentBudget

variable {sourceFactors finalFactors : List ActualFactorDatum}
  {ledger : RepeatedBadParentLedger sourceFactors finalFactors}
  {base : NNReal}

/-- Exact sum of the local `C_j` exponents. -/
def forwardExponent
    (B : RepeatedBadParentLocalExponentBudget ledger base) : Real :=
  (ledger.steps.map B.uniformityExponent).sum

/-- Exact sum of the local exponents of every `C_j * L_j`. -/
def reverseExponent
    (B : RepeatedBadParentLocalExponentBudget ledger base) : Real :=
  (ledger.steps.map fun step =>
    B.uniformityExponent step + B.freshRetentionExponent step).sum

/-- The forward product has exactly the sum of the displayed local
uniformity exponents. -/
theorem cumulativeForwardLoss_le_power
    (B : RepeatedBadParentLocalExponentBudget ledger base)
    (hbase : 0 < base) :
    cumulativeForwardLoss ledger <=
      (base : ENNReal) ^ (-B.forwardExponent) := by
  simpa only [cumulativeForwardLoss, forwardExponent] using
    (list_prod_le_rpow_neg_sum base hbase ledger.steps
      (fun step => step.uniformityLoss) B.uniformityExponent
      B.uniformity_upper)

/-- The reverse product has exactly the sum of the displayed local
uniformity and fresh-retention exponents. -/
theorem cumulativeReverseLoss_le_power
    (B : RepeatedBadParentLocalExponentBudget ledger base)
    (hbase : 0 < base) :
    cumulativeReverseLoss ledger <=
      (base : ENNReal) ^ (-B.reverseExponent) := by
  have hbase0 : (base : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hbase.ne'
  have hbaseTop : (base : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hstep : forall step, step ∈ ledger.steps ->
      step.uniformityLoss * step.freshRetentionLoss <=
        (base : ENNReal) ^
          (-(B.uniformityExponent step +
            B.freshRetentionExponent step)) := by
    intro step hmem
    calc
      step.uniformityLoss * step.freshRetentionLoss <=
          (base : ENNReal) ^ (-B.uniformityExponent step) *
            (base : ENNReal) ^ (-B.freshRetentionExponent step) :=
        mul_le_mul' (B.uniformity_upper step hmem)
          (B.freshRetention_upper step hmem)
      _ = (base : ENNReal) ^
          ((-B.uniformityExponent step) +
            (-B.freshRetentionExponent step)) := by
        rw [ENNReal.rpow_add _ _ hbase0 hbaseTop]
      _ = (base : ENNReal) ^
          (-(B.uniformityExponent step +
            B.freshRetentionExponent step)) := by
        congr 1
        ring
  simpa only [cumulativeReverseLoss, reverseExponent] using
    (list_prod_le_rpow_neg_sum base hbase ledger.steps
      (fun step => step.uniformityLoss * step.freshRetentionLoss)
      (fun step => B.uniformityExponent step +
        B.freshRetentionExponent step) hstep)

/-- A uniform pointwise exponent pair is a concrete local budget.  This is
the form expected when the paper chooses the same Definition 2.12 and fresh
loss budgets at every selector stage. -/
def ofUniform
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (base : NNReal) (uniformityExp freshExp : Real)
    (hUniformity : forall step, step ∈ ledger.steps ->
      step.uniformityLoss <= (base : ENNReal) ^ (-uniformityExp))
    (hFresh : forall step, step ∈ ledger.steps ->
      step.freshRetentionLoss <= (base : ENNReal) ^ (-freshExp)) :
    RepeatedBadParentLocalExponentBudget ledger base where
  uniformityExponent := fun _step => uniformityExp
  freshRetentionExponent := fun _step => freshExp
  uniformity_upper := hUniformity
  freshRetention_upper := hFresh

@[simp] theorem ofUniform_forwardExponent
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (base : NNReal) (uniformityExp freshExp : Real)
    (hUniformity : forall step, step ∈ ledger.steps ->
      step.uniformityLoss <= (base : ENNReal) ^ (-uniformityExp))
    (hFresh : forall step, step ∈ ledger.steps ->
      step.freshRetentionLoss <= (base : ENNReal) ^ (-freshExp)) :
    (ofUniform ledger base uniformityExp freshExp
      hUniformity hFresh).forwardExponent =
        (ledger.steps.length : Real) * uniformityExp := by
  simp [ofUniform, forwardExponent]

@[simp] theorem ofUniform_reverseExponent
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors)
    (base : NNReal) (uniformityExp freshExp : Real)
    (hUniformity : forall step, step ∈ ledger.steps ->
      step.uniformityLoss <= (base : ENNReal) ^ (-uniformityExp))
    (hFresh : forall step, step ∈ ledger.steps ->
      step.freshRetentionLoss <= (base : ENNReal) ^ (-freshExp)) :
    (ofUniform ledger base uniformityExp freshExp
      hUniformity hFresh).reverseExponent =
        (ledger.steps.length : Real) * (uniformityExp + freshExp) := by
  simp [ofUniform, reverseExponent, mul_add]

end RepeatedBadParentLocalExponentBudget

/-! ## The two consumer envelopes from a finite paper run -/

/-- The reconstructed source radius is definitionally the genuine source
factor-radius product and is therefore positive for every paper-ready run. -/
theorem reconstructedSourceRadius_pos_of_paperFactorFiniteRun
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    0 < reconstructedSourceRadius run.productLedger := by
  unfold reconstructedSourceRadius
  rw [<- run.productLedger.source_radiusProduct_eq_fixedLoss_pow_length_mul]
  exact factorRadiusProduct_pos_of_readiness sourceState.readiness

/-- The same reconstructed radius lies in the closed unit interval. -/
theorem reconstructedSourceRadius_le_one_of_paperFactorFiniteRun
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState) :
    reconstructedSourceRadius run.productLedger <= 1 := by
  unfold reconstructedSourceRadius
  rw [<- run.productLedger.source_radiusProduct_eq_fixedLoss_pow_length_mul]
  exact factorRadiusProduct_le_one_of_readiness sourceState.readiness

/-- Pointwise local exponent estimates and two transparent sum budgets
produce exactly the two envelopes required by the correlated Eq. 66
connector. -/
theorem power_envelopes_of_paperFactorFiniteRun_localBudget
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    (B : RepeatedBadParentLocalExponentBudget run.productLedger
      (reconstructedSourceRadius run.productLedger))
    {countExponent outerExponent : Real}
    (hForwardExponent : B.forwardExponent <= countExponent)
    (hReverseExponent : B.reverseExponent <= outerExponent) :
    cumulativeForwardLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-countExponent) /\
      cumulativeReverseLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-outerExponent) := by
  let base := reconstructedSourceRadius run.productLedger
  have hbase : 0 < base :=
    reconstructedSourceRadius_pos_of_paperFactorFiniteRun run
  have hbaseOne : (base : ENNReal) <= 1 := by
    exact_mod_cast
      reconstructedSourceRadius_le_one_of_paperFactorFiniteRun run
  have hForward := B.cumulativeForwardLoss_le_power hbase
  have hReverse := B.cumulativeReverseLoss_le_power hbase
  constructor
  · calc
      cumulativeForwardLoss run.productLedger <=
          (base : ENNReal) ^ (-B.forwardExponent) := hForward
      _ <= (base : ENNReal) ^ (-countExponent) := by
        apply ENNReal.rpow_le_rpow_of_exponent_ge hbaseOne
        linarith
  · calc
      cumulativeReverseLoss run.productLedger <=
          (base : ENNReal) ^ (-B.reverseExponent) := hReverse
      _ <= (base : ENNReal) ^ (-outerExponent) := by
        apply ENNReal.rpow_le_rpow_of_exponent_ge hbaseOne
        linarith

/-- Arithmetic adapter for a caller-supplied V1 run.  Although its local
power algebra is valid, V1 permits freely supplied stage certificates, so
this theorem is not a grounded top-level producer.  It is retained under an
explicit name for low-level consumers only. -/
theorem power_envelopes_uniformLocalBudget_of_suppliedV1Run
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    {uniformityExp freshExp : Real}
    (hUniformityExp : 0 <= uniformityExp)
    (hFreshExp : 0 <= freshExp)
    (hUniformity : forall step, step ∈ run.productLedger.steps ->
      step.uniformityLoss <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp))
    (hFresh : forall step, step ∈ run.productLedger.steps ->
      step.freshRetentionLoss <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-freshExp)) :
    cumulativeForwardLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-((N : Real) * uniformityExp)) /\
      cumulativeReverseLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-((N : Real) * (uniformityExp + freshExp))) := by
  let base := reconstructedSourceRadius run.productLedger
  let B := RepeatedBadParentLocalExponentBudget.ofUniform
    run.productLedger base uniformityExp freshExp hUniformity hFresh
  have hlength : (run.productLedger.steps.length : Real) <= (N : Real) := by
    exact_mod_cast run.productLedger_steps_length_le_N
  apply power_envelopes_of_paperFactorFiniteRun_localBudget run B
  · rw [RepeatedBadParentLocalExponentBudget.ofUniform_forwardExponent]
    exact mul_le_mul_of_nonneg_right hlength hUniformityExp
  · rw [RepeatedBadParentLocalExponentBudget.ofUniform_reverseExponent]
    exact mul_le_mul_of_nonneg_right hlength
      (add_nonneg hUniformityExp hFreshExp)

/-- Top-level uniform local exponent producer on the selector-grounded V2
run.  The edge bound is obtained from
`GroundedPaperFactorFiniteRun.productLedger_steps_length_le_N`, whose stage
progress was derived from literal first-crossing barriers. -/
theorem power_envelopes_of_groundedPaperFactorFiniteRun_uniformLocalBudget
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    {uniformityExp freshExp : Real}
    (hUniformityExp : 0 <= uniformityExp)
    (hFreshExp : 0 <= freshExp)
    (hUniformity : forall step, step ∈ run.productLedger.steps ->
      step.uniformityLoss <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp))
    (hFresh : forall step, step ∈ run.productLedger.steps ->
      step.freshRetentionLoss <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-freshExp)) :
    cumulativeForwardLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-((N : Real) * uniformityExp)) /\
      cumulativeReverseLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-((N : Real) * (uniformityExp + freshExp))) := by
  let v1 := run.toPaperFactorFiniteRun
  have hUniformityV1 : forall step, step ∈ v1.productLedger.steps ->
      step.uniformityLoss <=
        ((reconstructedSourceRadius v1.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp) := by
    simpa only [v1, GroundedPaperFactorFiniteRun.productLedger] using
      hUniformity
  have hFreshV1 : forall step, step ∈ v1.productLedger.steps ->
      step.freshRetentionLoss <=
        ((reconstructedSourceRadius v1.productLedger : NNReal) : ENNReal) ^
          (-freshExp) := by
    simpa only [v1, GroundedPaperFactorFiniteRun.productLedger] using hFresh
  let base := reconstructedSourceRadius v1.productLedger
  let B := RepeatedBadParentLocalExponentBudget.ofUniform
    v1.productLedger base uniformityExp freshExp hUniformityV1 hFreshV1
  have hlengthRun :
      (run.productLedger.steps.length : Real) <= (N : Real) := by
    exact_mod_cast run.productLedger_steps_length_le_N
  have hlength : (v1.productLedger.steps.length : Real) <= (N : Real) := by
    simpa only [v1, GroundedPaperFactorFiniteRun.productLedger] using
      hlengthRun
  have hForwardExponent : B.forwardExponent <=
      (N : Real) * uniformityExp := by
    dsimp only [B]
    rw [RepeatedBadParentLocalExponentBudget.ofUniform_forwardExponent]
    exact mul_le_mul_of_nonneg_right hlength hUniformityExp
  have hReverseExponent : B.reverseExponent <=
      (N : Real) * (uniformityExp + freshExp) := by
    dsimp only [B]
    rw [RepeatedBadParentLocalExponentBudget.ofUniform_reverseExponent]
    exact mul_le_mul_of_nonneg_right hlength
      (add_nonneg hUniformityExp hFreshExp)
  have H := power_envelopes_of_paperFactorFiniteRun_localBudget
    v1 B hForwardExponent hReverseExponent
  simpa only [v1, GroundedPaperFactorFiniteRun.productLedger] using H

/-! ## Automatic absorption of finite step losses below an explicit threshold -/

/-- The earliest finiteness data missing from the scalar transition type:
every displayed `C_j` and `L_j` is finite. -/
structure RepeatedBadParentFiniteLossData
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) : Prop where
  uniformityLoss_ne_top : forall step, step ∈ ledger.steps ->
    step.uniformityLoss ≠ ∞
  freshRetentionLoss_ne_top : forall step, step ∈ ledger.steps ->
    step.freshRetentionLoss ≠ ∞

namespace RepeatedBadParentFiniteLossData

variable {sourceFactors finalFactors : List ActualFactorDatum}
  {ledger : RepeatedBadParentLedger sourceFactors finalFactors}

/-- A list product of pointwise finite `ENNReal` values is finite. -/
theorem list_prod_ne_top
    (steps : List BadParentProductStep)
    (value : BadParentProductStep -> ENNReal)
    (hvalue : forall step, step ∈ steps -> value step ≠ ∞) :
    (steps.map value).prod ≠ ∞ := by
  induction steps with
  | nil => simp
  | cons step tail ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ENNReal.mul_ne_top (hvalue step (by simp))
        (ih (fun next hnext => hvalue next (by simp [hnext])))

theorem cumulativeForwardLoss_ne_top
    (F : RepeatedBadParentFiniteLossData ledger) :
    cumulativeForwardLoss ledger ≠ ∞ := by
  exact list_prod_ne_top ledger.steps (fun step => step.uniformityLoss)
    F.uniformityLoss_ne_top

theorem cumulativeReverseLoss_ne_top
    (F : RepeatedBadParentFiniteLossData ledger) :
    cumulativeReverseLoss ledger ≠ ∞ := by
  apply list_prod_ne_top ledger.steps
    (fun step => step.uniformityLoss * step.freshRetentionLoss)
  intro step hmem
  exact ENNReal.mul_ne_top (F.uniformityLoss_ne_top step hmem)
    (F.freshRetentionLoss_ne_top step hmem)

end RepeatedBadParentFiniteLossData

/-- Explicit common threshold which absorbs the two literal cumulative
products into prescribed positive exponents.  This threshold depends on the
already selected `run`; it is only a datum-local absorption theorem and is
not a uniform top-level smallness threshold. -/
def paperFactorFiniteRunPowerEnvelopeThreshold
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    (countExponent outerExponent : Real) : NNReal :=
  min
    (finiteConstantSmallDeltaThreshold
      (cumulativeForwardLoss run.productLedger) countExponent)
    (finiteConstantSmallDeltaThreshold
      (cumulativeReverseLoss run.productLedger) outerExponent)

theorem paperFactorFiniteRunPowerEnvelopeThreshold_pos
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    (countExponent outerExponent : Real) :
    0 < paperFactorFiniteRunPowerEnvelopeThreshold run
      countExponent outerExponent := by
  exact lt_min
    (finiteConstantSmallDeltaThreshold_pos
      (cumulativeForwardLoss run.productLedger) countExponent)
    (finiteConstantSmallDeltaThreshold_pos
      (cumulativeReverseLoss run.productLedger) outerExponent)

/-- If every literal step loss is finite, the existing finite-constant
small-scale producer gives both consumer envelopes below the explicit common
threshold.  No cumulative envelope is an input. -/
theorem power_envelopes_of_paperFactorFiniteRun_finiteLoss
    {N sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : PaperFactorFiniteRun N sourceStage finalStage
      sourceState finalState)
    (F : RepeatedBadParentFiniteLossData run.productLedger)
    {countExponent outerExponent : Real}
    (hCountExponent : 0 < countExponent)
    (hOuterExponent : 0 < outerExponent)
    (hsmall : reconstructedSourceRadius run.productLedger <=
      paperFactorFiniteRunPowerEnvelopeThreshold run
        countExponent outerExponent) :
    cumulativeForwardLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-countExponent) /\
      cumulativeReverseLoss run.productLedger <=
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-outerExponent) := by
  have hbase : 0 < reconstructedSourceRadius run.productLedger :=
    reconstructedSourceRadius_pos_of_paperFactorFiniteRun run
  constructor
  · exact finiteConstant_le_delta_negativePower
      F.cumulativeForwardLoss_ne_top hCountExponent hbase
      (hsmall.trans (min_le_left _ _))
  · exact finiteConstant_le_delta_negativePower
      F.cumulativeReverseLoss_ne_top hOuterExponent hbase
      (hsmall.trans (min_le_right _ _))

#print axioms factorRadiusProduct_pos_of_readiness
#print axioms factorRadiusProduct_le_one_of_readiness
#print axioms list_prod_le_rpow_neg_sum
#print axioms
  RepeatedBadParentLocalExponentBudget.cumulativeForwardLoss_le_power
#print axioms
  RepeatedBadParentLocalExponentBudget.cumulativeReverseLoss_le_power
#print axioms power_envelopes_of_paperFactorFiniteRun_localBudget
#print axioms
  RepeatedBadParentLocalExponentBudget.ofUniform_forwardExponent
#print axioms
  power_envelopes_uniformLocalBudget_of_suppliedV1Run
#print axioms
  power_envelopes_of_groundedPaperFactorFiniteRun_uniformLocalBudget
#print axioms
  RepeatedBadParentFiniteLossData.cumulativeForwardLoss_ne_top
#print axioms
  RepeatedBadParentFiniteLossData.cumulativeReverseLoss_ne_top
#print axioms paperFactorFiniteRunPowerEnvelopeThreshold_pos
#print axioms power_envelopes_of_paperFactorFiniteRun_finiteLoss

end
end Family8PaperFactorFiniteRunPowerEnvelopeV1
