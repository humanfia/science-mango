import FamilyStickyGrounding.FamilyStickyScaleChainActualDividingRunV1

set_option autoImplicit false

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainExponentProductBudgetV1

open Submission.Kakeya.ConvexFactoring
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesChainAtEveryAdapterV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainFiniteDeltaMaxBridgeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain

noncomputable section

/-!
# Sticky Kakeya: exponent accounting for actual buffered scale chains

This module replaces the monolithic product-budget input by three local,
source-shaped obligations: one exponent bound for every actual local factor,
one exponent bound for the literal endpoint volume ratio, and an equality
accounting for the total exponent.  The finite product and its `rpow`
arithmetic are proved here.
-/

/-- Pointwise powers of one finite base multiply to the power of the sum of
their exponents. -/
theorem prod_range_le_rpow_sum
    (base : ENNReal) (hbase_zero : base ≠ 0) (hbase_top : base ≠ ∞)
    (value : Nat -> ENNReal) (exponent : Nat -> Real) (depth : Nat)
    (hvalue : forall l, l < depth -> value l <= base ^ exponent l) :
    (∏ l ∈ Finset.range depth, value l) <=
      base ^ (∑ l ∈ Finset.range depth, exponent l) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      calc
        (∏ l ∈ Finset.range depth, value l) * value depth <=
            base ^ (∑ l ∈ Finset.range depth, exponent l) *
              base ^ exponent depth := by
          exact mul_le_mul' (ih (fun l hl => hvalue l (Nat.lt_succ_of_lt hl)))
            (hvalue depth (Nat.lt_succ_self depth))
        _ = base ^ ((∑ l ∈ Finset.range depth, exponent l) +
            exponent depth) := by
          rw [ENNReal.rpow_add _ _ hbase_zero hbase_top]

/-- A local-factor exponent bound and a separate endpoint exponent bound give
the combined product exponent. -/
theorem prod_mul_endpoint_le_rpow_sum_add
    (base : ENNReal) (hbase_zero : base ≠ 0) (hbase_top : base ≠ ∞)
    (value : Nat -> ENNReal) (exponent : Nat -> Real) (depth : Nat)
    (endpoint : ENNReal) (endpointExponent : Real)
    (hvalue : forall l, l < depth -> value l <= base ^ exponent l)
    (hendpoint : endpoint <= base ^ endpointExponent) :
    (∏ l ∈ Finset.range depth, value l) * endpoint <=
      base ^ ((∑ l ∈ Finset.range depth, exponent l) +
        endpointExponent) := by
  calc
    (∏ l ∈ Finset.range depth, value l) * endpoint <=
        base ^ (∑ l ∈ Finset.range depth, exponent l) *
          base ^ endpointExponent := by
      exact mul_le_mul'
        (prod_range_le_rpow_sum base hbase_zero hbase_top value exponent
          depth hvalue)
        hendpoint
    _ = base ^ ((∑ l ∈ Finset.range depth, exponent l) +
        endpointExponent) := by
      rw [ENNReal.rpow_add _ _ hbase_zero hbase_top]

namespace BufferedChainFamily

variable {outerDepth chainDepth stage : Nat}
  {delta : NNReal} {N : Nat} {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta outerDepth}

/-- Primitive exponent data for all actual buffered terminal chains.  None of
the fields is a product-budget or a threshold conclusion. -/
structure ExponentBudgetData
    (B : BufferedChainFamily outerDepth chainDepth)
    (S : FiniteScaleSequence delta outerDepth) (stage : Nat)
    (eta : Nat -> Real) where
  theta_pos : forall m, 0 < S.theta m
  localExponent : Fin outerDepth -> Nat -> Real
  endpointExponent : Fin outerDepth -> Real
  localFactor_upper : forall m l, l < chainDepth ->
    FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
        (B.hierarchy m) (B.datum m) l <=
      (S.theta m : ENNReal) ^ localExponent m l
  endpointRatio_upper : forall m,
    ((MeasureTheory.volume ((B.datum m).testBody chainDepth : Set
          LeanEval.Analysis.WangZahlKakeya.Space) /
        MeasureTheory.volume ((B.datum m).testBody 0 : Set
          LeanEval.Analysis.WangZahlKakeya.Space)) *
      ((B.datum m).tubeVolume 0 / (B.datum m).tubeVolume chainDepth)) <=
        (S.theta m : ENNReal) ^ endpointExponent m
  exponent_balance : forall m,
    (∑ l ∈ Finset.range chainDepth, localExponent m l) +
        endpointExponent m = -eta (stage - 1)

/-- The explicit local and endpoint exponent accounting produces the exact
actual product budget consumed by the finite Delta-max bridge. -/
theorem ExponentBudgetData.actualProductBudget
    (B : BufferedChainFamily outerDepth chainDepth)
    (E : ExponentBudgetData B S stage eta) : forall m,
    (∏ l ∈ Finset.range chainDepth,
      FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
        (B.hierarchy m) (B.datum m) l) *
      ((MeasureTheory.volume ((B.datum m).testBody chainDepth : Set
          LeanEval.Analysis.WangZahlKakeya.Space) /
        MeasureTheory.volume ((B.datum m).testBody 0 : Set
          LeanEval.Analysis.WangZahlKakeya.Space)) *
        ((B.datum m).tubeVolume 0 /
          (B.datum m).tubeVolume chainDepth)) <=
      (S.theta m : ENNReal) ^ (-eta (stage - 1)) := by
  intro m
  have htheta_zero : (S.theta m : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (E.theta_pos m))
  have htheta_top : (S.theta m : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  rw [← E.exponent_balance m]
  exact prod_mul_endpoint_le_rpow_sum_add
    (S.theta m : ENNReal) htheta_zero htheta_top
    (fun l =>
      FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
        (B.hierarchy m) (B.datum m) l)
    (E.localExponent m) chainDepth
    ((MeasureTheory.volume ((B.datum m).testBody chainDepth : Set
          LeanEval.Analysis.WangZahlKakeya.Space) /
        MeasureTheory.volume ((B.datum m).testBody 0 : Set
          LeanEval.Analysis.WangZahlKakeya.Space)) *
      ((B.datum m).tubeVolume 0 / (B.datum m).tubeVolume chainDepth))
    (E.endpointExponent m) (E.localFactor_upper m)
    (E.endpointRatio_upper m)

/-- End-to-end actual no-split run with the product budget synthesized from
explicit exponent data. -/
def toActualKatzTaoChainNoSplitRun_of_exponentData
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (E : ExponentBudgetData B S stage eta)
    (adjacent_upper : forall m,
      A.adjacentCoarseValue m <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1)))
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    KatzTaoChainNoSplitRun delta outerDepth chainDepth N epsilon eta S :=
  FamilyStickyScaleChainActualDividingRunV1.toActualKatzTaoChainNoSplitRun
    A B stage stage_pos stage_le eta_monotone eta_stage_le_epsilon
    (E.actualProductBudget B) adjacent_upper terminal_noSplit

/-- The fully accounted actual data yields the all-large versus dividing
witness dichotomy without a global product-budget callback. -/
theorem allLarge_or_witness_of_exponentData
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (eta_stage_le_epsilon : eta stage <= epsilon)
    (E : ExponentBudgetData B S stage eta)
    (adjacent_upper : forall m,
      A.adjacentCoarseValue m <=
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ eta (stage - 1)))
    (terminal_noSplit : forall m, ¬ S.IsLarge epsilon m ->
      ¬ (exists rho, S.IsBuffered epsilon m rho ∧
        A.coarseValueAt m rho <
          (((S.theta m / rho : NNReal) : ENNReal) ^ eta stage))) :
    S.AllStepsLarge epsilon ∨
      Nonempty (KatzTaoDividingWitness delta N epsilon eta) := by
  exact (toActualKatzTaoChainNoSplitRun_of_exponentData A B stage stage_pos
    stage_le eta_monotone eta_stage_le_epsilon E adjacent_upper
    terminal_noSplit).allLarge_or_witness

end BufferedChainFamily

#print axioms prod_range_le_rpow_sum
#print axioms prod_mul_endpoint_le_rpow_sum_add
#print axioms BufferedChainFamily.ExponentBudgetData.actualProductBudget
#print axioms BufferedChainFamily.toActualKatzTaoChainNoSplitRun_of_exponentData
#print axioms BufferedChainFamily.allLarge_or_witness_of_exponentData

end
end FamilyStickyScaleChainExponentProductBudgetV1
