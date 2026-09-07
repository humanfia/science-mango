import Family8Grounding.Family8ExactUniformDiscreteLongIntervalBootstrapV3
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1

/-!
# Exact-uniform discrete long-interval bootstrap, robust source budgets

This is the add-only successor of V4.  The two cast/algebra steps are exposed
as separate small lemmas before the final endpoint is elaborated.  In
particular the endpoint does not ask Lean to synthesize either intermediate
budget while elaborating the large long-interval expression.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExactUniformDiscreteLongIntervalBootstrapV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8ExactUniformDiscreteLongIntervalBootstrapV1
open Family8ExactUniformDiscreteLongIntervalBootstrapV2
open Family8ExactUniformDiscreteLongIntervalBootstrapV3
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- Clearing the exact lower-parent-density denominator rewrites the long
Katz--Tao budget as a source/branching inequality. -/
theorem exactUniformCoarseKatzTao_longBudget_of_branchingBudget
    {delta b : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {coarse : UniformTubeFamily b (Fin coarseCard)}
    (Ppart : CoarseTubePartition fine coarse)
    (hloss : Ppart.branchingLoss = 1)
    (hcoarse : Ppart.coarseIndices.Nonempty)
    (hdelta : 0 < delta) (hb : 0 < b)
    (sourceA target : NNReal)
    (hbranchBudget :
      8192 * sourceA * b ^ 2 <=
        target * (Ppart.branching : NNReal) * (delta ^ 2 / 2)) :
    1024 * exactUniformCoarseKatzTaoNNReal sourceA Ppart <= target := by
  have hlower : 0 < exactBranchingParentMassDensityNNReal Ppart :=
    exactBranchingParentMassDensityNNReal_pos
      Ppart hloss hcoarse hdelta hb
  rw [mul_comm]
  unfold exactUniformCoarseKatzTaoNNReal
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hlower).2
  unfold exactBranchingParentMassDensityNNReal
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < (8 * b ^ 2 : NNReal))).2
  convert hbranchBudget using 1 <;> ring

/-- Cast the source/fine-card budget once, independently of the long endpoint. -/
theorem exactUniformCoarseKatzTao_cardScaleBudgetENNReal_of_fineCardBudget
    {delta b : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {coarse : UniformTubeFamily b (Fin coarseCard)}
    (Ppart : CoarseTubePartition fine coarse)
    (hloss : Ppart.branchingLoss = 1)
    (hcoarse : Ppart.coarseIndices.Nonempty)
    (hdelta : 0 < delta) (hb : 0 < b)
    (sourceA C : NNReal)
    (hfineBudget :
      8192 * sourceA <=
        C * (Ppart.fineIndices.card : NNReal) * (delta ^ 2 / 2)) :
    (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 <=
      (C : ENNReal) *
        ((exactPartitionStickyCover Ppart).activeCoarse.card : ENNReal) *
        ((b : ENNReal) ^ 2 / 2) := by
  have hNN :
      exactUniformCoarseKatzTaoNNReal sourceA Ppart * 512 <=
        C * ((exactPartitionStickyCover Ppart).activeCoarse.card : NNReal) *
          (b ^ 2 / 2) :=
    exactUniformCoarseKatzTao_cardScaleBudget_of_fineCardBudget
      Ppart hloss hcoarse hdelta hb sourceA C hfineBudget
  have hcast := ENNReal.coe_le_coe.mpr hNN
  simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat,
    ENNReal.coe_natCast, ENNReal.coe_pow,
    ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)] using hcast

/-- Complete literal long endpoint from the two actual source-side budgets.
The datum namespace is explicit so this theorem remains stable under fresh
standalone compilation. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_exactUniformSourceBudgets
    {delta b globalDelta : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    {epsilon0 beta gamma : Real}
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (coarse : UniformTubeFamily b (Fin coarseCard))
    (Ppart : CoarseTubePartition D.family coarse)
    (hloss : Ppart.branchingLoss = 1)
    (hcoarse : Ppart.coarseIndices.Nonempty)
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (sourceA : NNReal)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta <= 1)
    (hglobalB : globalDelta <= b)
    (hbUpper : b <= globalDelta ^ (1 - P.epsilon))
    (hbHalf : b <= (2 : NNReal)⁻¹)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hFineCardBudget :
      8192 * sourceA <=
        globalDelta ^
            (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
              P j) *
          (Ppart.fineIndices.card : NNReal) * (delta ^ 2 / 2))
    (hBranchingBudget :
      8192 * sourceA * b ^ 2 <=
        globalDelta ^
            (-longIntervalDeltaLoss P.epsilon
              (10 * P.eta j / (P.epsilon * beta))) *
          (Ppart.branching : NNReal) * (delta ^ 2 / 2))
    (hglobalSmall : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hsourceKT : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily) :
    longIntervalKatzTaoRHSENNReal
        globalDelta b
        (activeCoarseCardScaleMass (exactPartitionStickyCover Ppart))
        P.epsilon (10 * P.eta j / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        globalDelta b
        (activeCoarseCardScaleMass (exactPartitionStickyCover Ppart))
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  have hb : 0 < b := hglobal.trans_le hglobalB
  have hCFBudget :=
    exactUniformCoarseKatzTao_cardScaleBudgetENNReal_of_fineCardBudget
      Ppart hloss hcoarse hD.delta_pos hb sourceA
      (globalDelta ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j))
      hFineCardBudget
  have hCFBudget' :
      (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 <=
        (globalDelta : ENNReal) ^
            (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
              P j) *
          ((exactPartitionStickyCover Ppart).activeCoarse.card : ENNReal) *
          ((b : ENNReal) ^ 2 / 2) := by
    simpa only [ENNReal.coe_rpow_of_ne_zero hglobal.ne'] using hCFBudget
  have hAKT :=
    exactUniformCoarseKatzTao_longBudget_of_branchingBudget
      Ppart hloss hcoarse hD.delta_pos hb sourceA
      (globalDelta ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta j / (P.epsilon * beta))))
      hBranchingBudget
  exact
    Family8ExactUniformDiscreteLongIntervalBootstrapV2.longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_exactUniformScalarBudgets
      D hD coarse Ppart hloss hcoarse P j sourceA
      hglobal hglobalOne hglobalB hbUpper hbHalf hbeta hgamma
      hCFBudget' hglobalSmall hsourceKT hAKT

#print axioms exactUniformCoarseKatzTao_longBudget_of_branchingBudget
#print axioms
  exactUniformCoarseKatzTao_cardScaleBudgetENNReal_of_fineCardBudget
#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_exactUniformSourceBudgets

end
end Family8ExactUniformDiscreteLongIntervalBootstrapV5
