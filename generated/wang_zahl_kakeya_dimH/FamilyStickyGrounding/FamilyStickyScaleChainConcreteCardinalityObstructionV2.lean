import FamilyStickyGrounding.FamilyStickyScaleChainConcreteAutomaticNumericsV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainConcreteCardinalityObstructionV2

open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainUniformAutomaticThetaThresholdV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainFullyAutomaticDeltaThresholdV2
open FamilyStickyScaleChainConcreteAutomaticNumericsV2

noncomputable section

/-!
# Cardinality obstruction for the concrete automatic threshold

This diagnostic module isolates a limitation of the current concrete
automatic endpoint.  It uses no geometric packing statement: the finite
index type itself is allowed to grow.  The terminal finite constant makes
the concrete threshold at most the inverse square of an explicit quadratic
polynomial in its cardinality.  Consequently no positive threshold can be
uniform over all finite index types.
-/

/-- The padded finite constant occurring in the concrete one-step theta
threshold, written directly in `NNReal`. -/
def concreteAutomaticCardinalityPolynomial (n : Nat) : NNReal :=
  100 * (n : NNReal) ^ 2 + 250 * (n : NNReal) + 1

/-- Direct unpadded form, useful when unfolding the small-delta component. -/
theorem automaticTerminalAbsorptionConstant_formula (n : Nat) :
    automaticTerminalAbsorptionConstant n =
      ((100 * (n : NNReal) ^ 2 + 250 * n : NNReal) : ENNReal) := by
  simp only [automaticTerminalAbsorptionConstant,
    automaticTerminalFiniteConstant]
  push_cast
  ring

/-- With profile exponent three, the finite-constant component is exactly
the reciprocal of the padded quadratic cardinality polynomial. -/
theorem concreteAutomaticFiniteConstantComponent_formula (n : Nat) :
    finiteConstantSmallDeltaThreshold
        (automaticTerminalAbsorptionConstant n) 1 =
      (concreteAutomaticCardinalityPolynomial n)⁻¹ := by
  rw [finiteConstantSmallDeltaThreshold,
    automaticTerminalAbsorptionConstant_formula, ENNReal.toNNReal_coe]
  norm_num [concreteAutomaticCardinalityPolynomial, NNReal.rpow_neg_one]

/-- Already the first stage of the five-stage uniform minimum bounds the
concrete theta cap by the reciprocal quadratic cardinality factor. -/
theorem concreteAutomaticThetaCap_fin_le_cardinalityPolynomial_inv
    (n : Nat) :
    fullyAutomaticDeltaThetaCap (Fin n) concreteAutomaticEta
        concreteAutomaticStageBound <=
      (concreteAutomaticCardinalityPolynomial n)⁻¹ := by
  calc
    fullyAutomaticDeltaThetaCap (Fin n) concreteAutomaticEta
        concreteAutomaticStageBound <=
        automaticOneStepSmallThetaThreshold n 3 := by
      convert
        (uniformAutomaticThetaThreshold_le_stage n concreteAutomaticEta 5 0
          (by norm_num)) using 1 <;>
        simp [fullyAutomaticDeltaThetaCap, concreteAutomaticStageBound,
          concreteAutomaticEta]
    _ <= finiteConstantSmallDeltaThreshold
        (automaticTerminalAbsorptionConstant n) 1 := by
      change min (2 : NNReal)⁻¹
        (finiteConstantSmallDeltaThreshold
          (automaticTerminalAbsorptionConstant n) (3 - 2)) <=
        finiteConstantSmallDeltaThreshold
          (automaticTerminalAbsorptionConstant n) 1
      calc
        _ <= finiteConstantSmallDeltaThreshold
            (automaticTerminalAbsorptionConstant n) (3 - 2) :=
          min_le_right _ _
        _ = finiteConstantSmallDeltaThreshold
            (automaticTerminalAbsorptionConstant n) 1 := by norm_num
    _ = (concreteAutomaticCardinalityPolynomial n)⁻¹ :=
      concreteAutomaticFiniteConstantComponent_formula n

/-- The concrete total delta threshold is bounded by the inverse square of
the padded quadratic cardinality polynomial.  The square is forced by the
seed gap `1 / 2`; no direction-packing estimate is used. -/
theorem concreteAutomaticDeltaThreshold_fin_le_cardinalityPolynomial_inv_sq
    (n : Nat) :
    concreteAutomaticDeltaThreshold (Fin n) <=
      (concreteAutomaticCardinalityPolynomial n)⁻¹ ^ 2 := by
  calc
    concreteAutomaticDeltaThreshold (Fin n) <=
        cappedSeedDeltaThreshold
          (fullyAutomaticDeltaThetaCap (Fin n) concreteAutomaticEta
            concreteAutomaticStageBound)
          concreteAutomaticGap :=
      fullyAutomaticDeltaThreshold_le_seed (Fin n) concreteAutomaticEta
        concreteAutomaticStageBound concreteAutomaticGap
    _ <= (fullyAutomaticDeltaThetaCap (Fin n) concreteAutomaticEta
          concreteAutomaticStageBound) ^ (1 / concreteAutomaticGap) :=
      min_le_right _ _
    _ = (fullyAutomaticDeltaThetaCap (Fin n) concreteAutomaticEta
          concreteAutomaticStageBound) ^ 2 := by
      norm_num [concreteAutomaticGap]
    _ <= (concreteAutomaticCardinalityPolynomial n)⁻¹ ^ 2 := by
      gcongr
      exact concreteAutomaticThetaCap_fin_le_cardinalityPolynomial_inv n

/-- Parameterized obstruction: whenever the explicit inverse-square factor
has already fallen below a scale, the concrete automatic threshold for
`Fin n` is strictly smaller than that scale. -/
theorem concreteAutomaticDeltaThreshold_fin_lt_of_inv_sq_lt
    (n : Nat) (delta : NNReal)
    (explicit_lt :
      (concreteAutomaticCardinalityPolynomial n)⁻¹ ^ 2 < delta) :
    concreteAutomaticDeltaThreshold (Fin n) < delta :=
  (concreteAutomaticDeltaThreshold_fin_le_cardinalityPolynomial_inv_sq n).trans_lt
    explicit_lt

/-- The concrete thresholds on `Fin n` fall below every positive scale.
This is the purely cardinality-based obstruction; it assumes no relationship
between cardinality and a geometric tube radius. -/
theorem exists_fin_concreteAutomaticDeltaThreshold_lt
    (delta : NNReal) (delta_pos : 0 < delta) :
    exists n : Nat, concreteAutomaticDeltaThreshold (Fin n) < delta := by
  obtain ⟨n, hn⟩ := exists_nat_gt delta⁻¹
  let p : NNReal := concreteAutomaticCardinalityPolynomial n
  have n_pos : 0 < (n : NNReal) :=
    lt_of_le_of_lt (bot_le : (0 : NNReal) <= delta⁻¹) hn
  have n_inv_lt : (n : NNReal)⁻¹ < delta :=
    (inv_lt_comm₀ n_pos delta_pos).2 hn
  have n_le_p : (n : NNReal) <= p := by
    dsimp only [p, concreteAutomaticCardinalityPolynomial]
    calc
      (n : NNReal) <= 250 * n := by
        nth_rewrite 1 [← one_mul (n : NNReal)]
        gcongr
        norm_num
      _ <= 100 * (n : NNReal) ^ 2 + 250 * n :=
        le_add_of_nonneg_left (by positivity)
      _ <= 100 * (n : NNReal) ^ 2 + 250 * n + 1 :=
        le_add_of_nonneg_right (by positivity)
  have one_le_p : (1 : NNReal) <= p := by
    dsimp only [p, concreteAutomaticCardinalityPolynomial]
    exact le_add_of_nonneg_left (by positivity)
  have p_inv_le_n_inv : p⁻¹ <= (n : NNReal)⁻¹ :=
    inv_anti₀ n_pos n_le_p
  have p_inv_le_one : p⁻¹ <= 1 := by
    simpa using inv_anti₀ (by norm_num : (0 : NNReal) < 1) one_le_p
  refine ⟨n, (concreteAutomaticDeltaThreshold_fin_le_cardinalityPolynomial_inv_sq n).trans_lt ?_⟩
  change p⁻¹ ^ 2 < delta
  calc
    p⁻¹ ^ 2 = p⁻¹ * p⁻¹ := pow_two _
    _ <= p⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left p_inv_le_one (by positivity)
    _ = p⁻¹ := mul_one _
    _ <= (n : NNReal)⁻¹ := p_inv_le_n_inv
    _ < delta := n_inv_lt

/-- In particular, no positive cardinality-independent lower threshold can
work uniformly even for the canonical finite types `Fin n`. -/
theorem not_exists_positive_uniform_fin_concreteAutomaticDeltaThreshold :
    Not (exists delta0 : NNReal, 0 < delta0 /\
      forall n : Nat,
        delta0 <= concreteAutomaticDeltaThreshold (Fin n)) := by
  rintro ⟨delta0, delta0_pos, uniform⟩
  obtain ⟨n, threshold_lt⟩ :=
    exists_fin_concreteAutomaticDeltaThreshold_lt delta0 delta0_pos
  exact (not_lt_of_ge (uniform n)) threshold_lt

#print axioms automaticTerminalAbsorptionConstant_formula
#print axioms concreteAutomaticFiniteConstantComponent_formula
#print axioms concreteAutomaticThetaCap_fin_le_cardinalityPolynomial_inv
#print axioms concreteAutomaticDeltaThreshold_fin_le_cardinalityPolynomial_inv_sq
#print axioms concreteAutomaticDeltaThreshold_fin_lt_of_inv_sq_lt
#print axioms exists_fin_concreteAutomaticDeltaThreshold_lt
#print axioms not_exists_positive_uniform_fin_concreteAutomaticDeltaThreshold

end
end FamilyStickyScaleChainConcreteCardinalityObstructionV2
