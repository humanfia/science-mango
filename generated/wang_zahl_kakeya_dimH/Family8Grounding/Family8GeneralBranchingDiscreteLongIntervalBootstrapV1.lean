import Family8Grounding.Family8GeneralBranchingLowerParentMassV1
import Family8Grounding.Family8DiscreteLongIntervalEndpointBootstrapV1
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2

/-!
# General-branching discrete long-interval bootstrap

This successor removes exact uniformity from the literal selected endpoint.
The lower parent density and coarse Katz--Tao coefficient pay precisely the
declared branching loss of a `CoarseTubePartition`.  Thus the same endpoint
can consume a dyadic logarithmic-branching partition with loss two.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8GeneralBranchingDiscreteLongIntervalBootstrapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8DiscreteLongIntervalEndpointBootstrapV1
open Family8GeneralBranchingLowerParentMassV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- A selected-cardinality scale-mass budget bounds the canonical Frostman
constant for any genuine `CoarseTubePartition`; no exact branching identity
is required at this stage. -/
theorem exactPartitionStickyCover_canonicalFrostmanConstant_le_of_generalBranchingCardScaleBudget
    {delta b : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta iota)
    (hD : D.IsAdmissible)
    (coarse : UniformTubeFamily b (Fin coarseCard))
    (Ppart : CoarseTubePartition D.family coarse)
    (sourceA : NNReal) (C : ENNReal)
    (hb : 0 < b) (hbHalf : b <= (2 : NNReal)⁻¹)
    (hsourceKT : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily)
    (hbudget :
      (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 <=
        C *
          ((exactPartitionStickyCover Ppart).activeCoarse.card : ENNReal) *
          ((b : ENNReal) ^ 2 / 2)) :
    canonicalFrostmanConstant
        (exactPartitionStickyCover Ppart).activeCoarseFamily
        closedBallFourBody <= C := by
  let U := exactPartitionStickyCover Ppart
  have hcoarseU : U.activeCoarse.Nonempty := Ppart.coarseIndices_nonempty
  have hcontained : forall k,
      (U.activeCoarseFamily k : Set Space) <=
        (closedBallFourBody : Set Space) := by
    intro k
    simpa only [coe_closedBallFourBody] using
      activeCoarseFamily_body_subset_closedBall_four
        D hD U (hbHalf.trans (by norm_num)) k
  have hmass : containedMass U.activeCoarseFamily closedBallFourBody =
      familyVolume U.activeCoarseFamily :=
    containedMass_eq_familyVolume_of_contained
      U.activeCoarseFamily closedBallFourBody hcontained
  have hKTscale : U.IsKatzTaoAtScale
      (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) :=
      exactPartitionStickyCover_isKatzTaoAtScale_of_generalBranching
        Ppart hD.delta_pos hb hD.delta_le_half hbHalf sourceA hsourceKT
  have hKT : IsKatzTao
      (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal)
      U.activeCoarseFamily :=
    isKatzTao_iff_concentration_le.mpr hKTscale
  have hmassLower :
      (U.activeCoarse.card : ENNReal) * ((b : ENNReal) ^ 2 / 2) <=
        familyVolume U.activeCoarseFamily :=
    Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover.activeCoarse_card_mul_half_sq_le_familyVolume
      D U hbHalf
  have hbase :
      (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) *
          volume (closedBallFourBody : Set Space) <=
        C * containedMass U.activeCoarseFamily closedBallFourBody := by
    rw [hmass]
    calc
      (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) *
          volume (closedBallFourBody : Set Space) <=
          (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 :=
        mul_le_mul' le_rfl volume_closedBall_zero_four_le_512
      _ <= C * (U.activeCoarse.card : ENNReal) *
          ((b : ENNReal) ^ 2 / 2) := hbudget
      _ = C * ((U.activeCoarse.card : ENNReal) *
          ((b : ENNReal) ^ 2 / 2)) := by ring
      _ <= C * familyVolume U.activeCoarseFamily :=
        mul_le_mul' le_rfl hmassLower
  have hF : IsFrostmanIn C U.activeCoarseFamily closedBallFourBody :=
    IsKatzTao.isFrostmanIn hKT hcontained hbase
  apply canonicalFrostmanConstant_le_of_isFrostmanIn hF
  rw [hmass]
  exact
    (Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover.activeCoarseFamilyVolume_pos
      U hb hcoarseU).ne'

/-- The literal long endpoint for an arbitrary branching-loss partition.
Only its two normalized scalar budgets and the source Katz--Tao theorem
remain as analytic inputs. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_generalBranchingScalarBudgets
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
    (hCFBudget :
      (branchingLossCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 <=
        (globalDelta : ENNReal) ^
            (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
              P j) *
          ((exactPartitionStickyCover Ppart).activeCoarse.card : ENNReal) *
          ((b : ENNReal) ^ 2 / 2))
    (hglobalSmall : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hsourceKT : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily)
    (hAKT : 1024 * branchingLossCoarseKatzTaoNNReal sourceA Ppart <=
      globalDelta ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta j / (P.epsilon * beta)))) :
    longIntervalKatzTaoRHSENNReal
        globalDelta b
        (activeCoarseCardScaleMass (exactPartitionStickyCover Ppart))
        P.epsilon (10 * P.eta j / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        globalDelta b
        (activeCoarseCardScaleMass (exactPartitionStickyCover Ppart))
        (10 * P.eta j / (P.epsilon * beta)) gamma := by
  have hb : 0 < b := hglobal.trans_le hglobalB
  apply
    Family8DiscreteLongIntervalEndpointBootstrapV1.longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_discreteEndpoint
      D hD (exactPartitionStickyCover Ppart) P j
      (branchingLossCoarseKatzTaoNNReal sourceA Ppart)
      hglobal hglobalOne hglobalB hbUpper hbHalf
      Ppart.coarseIndices_nonempty hbeta hgamma
  · exact
      exactPartitionStickyCover_canonicalFrostmanConstant_le_of_generalBranchingCardScaleBudget
        D hD coarse Ppart sourceA
        ((globalDelta : ENNReal) ^
          (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
            P j))
        hb hbHalf hsourceKT hCFBudget
  · exact hglobalSmall
  · exact
      exactPartitionStickyCover_isKatzTaoAtScale_of_generalBranching
        Ppart hD.delta_pos hb hD.delta_le_half hbHalf sourceA hsourceKT
  · exact hAKT

#print axioms
  exactPartitionStickyCover_canonicalFrostmanConstant_le_of_generalBranchingCardScaleBudget
#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_generalBranchingScalarBudgets

end
end Family8GeneralBranchingDiscreteLongIntervalBootstrapV1
