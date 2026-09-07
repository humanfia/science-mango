import Family8Grounding.Family8ExactUniformDiscreteLongIntervalBootstrapV2

/-!
# Exact-uniform discrete long-interval bootstrap, source-card budget

Exact branching gives `fineCount = coarseCount * branching`.  Substituting
that identity into the V2 canonical-Frostman budget cancels the intermediate
radius completely.  The resulting sufficient input is a source-side budget
against the literal selected fine-cardinality scale mass.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExactUniformDiscreteLongIntervalBootstrapV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8ExactUniformDiscreteLongIntervalBootstrapV1
open Family8ExactUniformDiscreteLongIntervalBootstrapV2
open Family8JointTubeFactoringExactUniformProp66AProductV4
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- The exact branching/cardinality identity converts a source fine-card
normalization into the selected coarse canonical-Frostman scalar budget.
The constant is `512 * 8 * 4 = 16384`, written against `delta^2 / 2` as
`8192`. -/
theorem exactUniformCoarseKatzTao_cardScaleBudget_of_fineCardBudget
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
    exactUniformCoarseKatzTaoNNReal sourceA Ppart * 512 <=
      C * ((exactPartitionStickyCover Ppart).activeCoarse.card : NNReal) *
        (b ^ 2 / 2) := by
  have hbranchNat : 0 < Ppart.branching :=
    Family8ExactUniformLowerParentMassV2.branching_pos_of_coarseIndices_nonempty
      Ppart hloss hcoarse
  have hbranch : 0 < (Ppart.branching : NNReal) := by
    exact_mod_cast hbranchNat
  have hlower : 0 < exactBranchingParentMassDensityNNReal Ppart :=
    exactBranchingParentMassDensityNNReal_pos
      Ppart hloss hcoarse hdelta hb
  have hcardNat :
      Ppart.fineIndices.card =
        Ppart.coarseIndices.card * Ppart.branching :=
    fineIndices_card_eq_coarseIndices_card_mul_branching_of_branchingLoss_eq_one
      Ppart hloss
  have hcard :
      (Ppart.fineIndices.card : NNReal) =
        (Ppart.coarseIndices.card : NNReal) *
          (Ppart.branching : NNReal) := by
    exact_mod_cast hcardNat
  rw [hcard] at hfineBudget
  unfold exactUniformCoarseKatzTaoNNReal
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hlower).2
  unfold exactBranchingParentMassDensityNNReal
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < (8 * b ^ 2 : NNReal))).2
  have hmul := mul_le_mul_right hfineBudget (b ^ 2 / 2)
  convert hmul using 1 <;> ring

#print axioms
  exactUniformCoarseKatzTao_cardScaleBudget_of_fineCardBudget

end
end Family8ExactUniformDiscreteLongIntervalBootstrapV3
