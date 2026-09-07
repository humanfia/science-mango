import Family8Grounding.Family8GeneralBranchingDiscreteLongIntervalBootstrapV1

/-!
# General-branching discrete endpoint from source budgets

The upper fiber-cardinality bound costs two powers of `branchingLoss` in the
canonical-Frostman budget.  Clearing the lower-parent-density denominator in
the Katz--Tao budget costs one power.  For the logarithmic dyadic factoring
producer both losses are fixed numerical constants because its branching
loss is exactly two.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8GeneralBranchingDiscreteLongIntervalBootstrapV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8GeneralBranchingDiscreteLongIntervalBootstrapV1
open Family8GeneralBranchingLowerParentMassV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- The global upper fiber bound converts a fine-card source budget into the
coarse selected-card budget.  Approximate uniformity costs exactly the square
of the declared branching loss. -/
theorem branchingLossCoarseKatzTao_cardScaleBudget_of_fineCardBudget
    {delta b : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {coarse : UniformTubeFamily b (Fin coarseCard)}
    (Ppart : CoarseTubePartition fine coarse)
    (hdelta : 0 < delta) (hb : 0 < b)
    (sourceA C : NNReal)
    (hfineBudget :
      8192 * (Ppart.branchingLoss : NNReal) ^ 2 * sourceA <=
        C * (Ppart.fineIndices.card : NNReal) * (delta ^ 2 / 2)) :
    branchingLossCoarseKatzTaoNNReal sourceA Ppart * 512 <=
      C * ((exactPartitionStickyCover Ppart).activeCoarse.card : NNReal) *
        (b ^ 2 / 2) := by
  have hloss : 0 < (Ppart.branchingLoss : NNReal) := by
    exact_mod_cast Ppart.branchingLoss_pos
  have hlower : 0 < branchingLossParentMassDensityNNReal Ppart :=
    branchingLossParentMassDensityNNReal_pos Ppart hdelta hb
  have hcardNat := Ppart.card_fine_le_coarse_mul_loss_mul_branching
  have hcard :
      (Ppart.fineIndices.card : NNReal) <=
        (Ppart.coarseIndices.card : NNReal) *
          ((Ppart.branchingLoss : NNReal) *
            (Ppart.branching : NNReal)) := by
    exact_mod_cast hcardNat
  have hsourceUpper :
      8192 * (Ppart.branchingLoss : NNReal) ^ 2 * sourceA <=
        C * ((Ppart.coarseIndices.card : NNReal) *
          ((Ppart.branchingLoss : NNReal) *
            (Ppart.branching : NNReal))) * (delta ^ 2 / 2) :=
    hfineBudget.trans
      (mul_le_mul' (mul_le_mul' le_rfl hcard) le_rfl)
  have hcancelMul :
      (Ppart.branchingLoss : NNReal) *
          (8192 * (Ppart.branchingLoss : NNReal) * sourceA) <=
        (Ppart.branchingLoss : NNReal) *
          (C * (Ppart.coarseIndices.card : NNReal) *
            (Ppart.branching : NNReal) * (delta ^ 2 / 2)) := by
    calc
      (Ppart.branchingLoss : NNReal) *
          (8192 * (Ppart.branchingLoss : NNReal) * sourceA) =
          8192 * (Ppart.branchingLoss : NNReal) ^ 2 * sourceA := by ring
      _ <= C * ((Ppart.coarseIndices.card : NNReal) *
          ((Ppart.branchingLoss : NNReal) *
            (Ppart.branching : NNReal))) * (delta ^ 2 / 2) := hsourceUpper
      _ = (Ppart.branchingLoss : NNReal) *
          (C * (Ppart.coarseIndices.card : NNReal) *
            (Ppart.branching : NNReal) * (delta ^ 2 / 2)) := by ring
  have hcancel :
      8192 * (Ppart.branchingLoss : NNReal) * sourceA <=
        C * (Ppart.coarseIndices.card : NNReal) *
          (Ppart.branching : NNReal) * (delta ^ 2 / 2) :=
    le_of_mul_le_mul_left hcancelMul hloss
  unfold branchingLossCoarseKatzTaoNNReal
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hlower).2
  have hrhs :
      C * (Ppart.coarseIndices.card : NNReal) * (b ^ 2 / 2) *
          branchingLossParentMassDensityNNReal Ppart =
        (C * (Ppart.coarseIndices.card : NNReal) *
            (Ppart.branching : NNReal) * (delta ^ 2 / 2)) /
          (16 * (Ppart.branchingLoss : NNReal)) := by
    unfold branchingLossParentMassDensityNNReal effectiveBranchingNNReal
    field_simp [hloss.ne', hb.ne']
    ; ring
  rw [hrhs]
  apply (le_div_iff₀ (by positivity :
    0 < (16 * (Ppart.branchingLoss : NNReal)))).2
  convert hcancel using 1
  ring

/-- Clearing the general lower-parent-density denominator costs one power of
the declared branching loss in the long Katz--Tao budget. -/
theorem branchingLossCoarseKatzTao_longBudget_of_branchingBudget
    {delta b : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    {fine : UniformTubeFamily delta iota}
    {coarse : UniformTubeFamily b (Fin coarseCard)}
    (Ppart : CoarseTubePartition fine coarse)
    (hdelta : 0 < delta) (hb : 0 < b)
    (sourceA target : NNReal)
    (hbranchBudget :
      8192 * (Ppart.branchingLoss : NNReal) * sourceA * b ^ 2 <=
        target * (Ppart.branching : NNReal) * (delta ^ 2 / 2)) :
    1024 * branchingLossCoarseKatzTaoNNReal sourceA Ppart <= target := by
  have hloss : 0 < (Ppart.branchingLoss : NNReal) := by
    exact_mod_cast Ppart.branchingLoss_pos
  have hlower : 0 < branchingLossParentMassDensityNNReal Ppart :=
    branchingLossParentMassDensityNNReal_pos Ppart hdelta hb
  rw [mul_comm]
  unfold branchingLossCoarseKatzTaoNNReal
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hlower).2
  have hrhs :
      target * branchingLossParentMassDensityNNReal Ppart =
        (target * (Ppart.branching : NNReal) * (delta ^ 2 / 2)) /
          (8 * (Ppart.branchingLoss : NNReal) * b ^ 2) := by
    unfold branchingLossParentMassDensityNNReal effectiveBranchingNNReal
    field_simp [hloss.ne', hb.ne']
  rw [hrhs]
  apply (le_div_iff₀ (by positivity :
    0 < (8 * (Ppart.branchingLoss : NNReal) * b ^ 2))).2
  convert hbranchBudget using 1
  ring

/-- Complete arbitrary-loss literal endpoint from fine-card and branching
source budgets. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_generalBranchingSourceBudgets
    {delta b globalDelta : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    {epsilon0 beta gamma : Real}
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (coarse : UniformTubeFamily b (Fin coarseCard))
    (Ppart : CoarseTubePartition D.family coarse)
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (sourceA : NNReal)
    (hglobal : 0 < globalDelta) (hglobalOne : globalDelta <= 1)
    (hglobalB : globalDelta <= b)
    (hbUpper : b <= globalDelta ^ (1 - P.epsilon))
    (hbHalf : b <= (2 : NNReal)⁻¹)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hFineCardBudget :
      8192 * (Ppart.branchingLoss : NNReal) ^ 2 * sourceA <=
        globalDelta ^
            (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
              P j) *
          (Ppart.fineIndices.card : NNReal) * (delta ^ 2 / 2))
    (hBranchingBudget :
      8192 * (Ppart.branchingLoss : NNReal) * sourceA * b ^ 2 <=
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
  have hCFBudgetNN :=
    branchingLossCoarseKatzTao_cardScaleBudget_of_fineCardBudget
      Ppart hD.delta_pos hb sourceA
      (globalDelta ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j))
      hFineCardBudget
  have hCFBudget :
      (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 <=
        (globalDelta : ENNReal) ^
            (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
              P j) *
          ((exactPartitionStickyCover Ppart).activeCoarse.card : ENNReal) *
          ((b : ENNReal) ^ 2 / 2) := by
    have hcast := ENNReal.coe_le_coe.mpr hCFBudgetNN
    simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat,
      ENNReal.coe_natCast, ENNReal.coe_pow,
      ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
      ENNReal.coe_rpow_of_ne_zero hglobal.ne'] using hcast
  have hAKT :=
    branchingLossCoarseKatzTao_longBudget_of_branchingBudget
      Ppart hD.delta_pos hb sourceA
      (globalDelta ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta j / (P.epsilon * beta))))
      hBranchingBudget
  exact
    longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_generalBranchingScalarBudgets
      D hD coarse Ppart P j sourceA
      hglobal hglobalOne hglobalB hbUpper hbHalf hbeta hgamma
      hCFBudget hglobalSmall hsourceKT hAKT

#print axioms
  branchingLossCoarseKatzTao_cardScaleBudget_of_fineCardBudget
#print axioms
  branchingLossCoarseKatzTao_longBudget_of_branchingBudget
#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_generalBranchingSourceBudgets

end
end Family8GeneralBranchingDiscreteLongIntervalBootstrapV2
