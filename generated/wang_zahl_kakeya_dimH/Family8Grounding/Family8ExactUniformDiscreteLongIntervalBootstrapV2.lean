import Family8Grounding.Family8ExactUniformDiscreteLongIntervalBootstrapV1
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2

/-!
# Exact-uniform discrete long-interval bootstrap, scalar-only endpoint

The exact-uniform Katz--Tao certificate also controls the canonical Frostman
constant once its fixed-ball numerator is normalized by the actual selected
coarse mass.  Uniform tube geometry replaces that mass by the literal
selected-cardinality scale mass.  Hence the endpoint's remaining analytic
inputs are two explicit scalar budgets; no coherent-cover or separate
Frostman certificate remains.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExactUniformDiscreteLongIntervalBootstrapV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.JointTubeFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8ExactUniformDiscreteLongIntervalBootstrapV1
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

/-- A selected-cardinality scale-mass budget forces the canonical Frostman
constant bound on the same exact-uniform endpoint. -/
theorem exactPartitionStickyCover_canonicalFrostmanConstant_le_of_cardScaleBudget
    {delta b : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (coarse : UniformTubeFamily b (Fin coarseCard))
    (Ppart : CoarseTubePartition D.family coarse)
    (hloss : Ppart.branchingLoss = 1)
    (hcoarse : Ppart.coarseIndices.Nonempty)
    (sourceA : NNReal) (C : ENNReal)
    (hb : 0 < b) (hbHalf : b <= (2 : NNReal)⁻¹)
    (hsourceKT : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily)
    (hbudget :
      (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 <=
        C *
          ((exactPartitionStickyCover Ppart).activeCoarse.card : ENNReal) *
          ((b : ENNReal) ^ 2 / 2)) :
    canonicalFrostmanConstant
        (exactPartitionStickyCover Ppart).activeCoarseFamily
        closedBallFourBody <= C := by
  let U := exactPartitionStickyCover Ppart
  have hcoarseU : U.activeCoarse.Nonempty := hcoarse
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
      (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) := by
    rw [coe_exactUniformCoarseKatzTaoNNReal
      sourceA Ppart hloss hcoarse hD.delta_pos hb]
    exact
      Family8ExactUniformLowerParentMassV2.exactPartitionStickyCover_isKatzTaoAtScale_of_source
        Ppart hloss hcoarse hD.delta_pos hb hD.delta_le_half hbHalf hsourceKT
  have hKT : IsKatzTao
      (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal)
      U.activeCoarseFamily :=
    isKatzTao_iff_concentration_le.mpr hKTscale
  have hmassLower :
      (U.activeCoarse.card : ENNReal) * ((b : ENNReal) ^ 2 / 2) <=
        familyVolume U.activeCoarseFamily :=
    Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover.activeCoarse_card_mul_half_sq_le_familyVolume
      D U hbHalf
  have hbase :
      (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) *
          volume (closedBallFourBody : Set Space) <=
        C * containedMass U.activeCoarseFamily closedBallFourBody := by
    rw [hmass]
    calc
      (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) *
          volume (closedBallFourBody : Set Space) <=
          (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 :=
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

/-- The literal selected endpoint closes the long-interval scalar argument
from two explicit budgets: one for its normalized canonical constant and one
for its Katz--Tao contribution. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_exactUniformScalarBudgets
    {delta b globalDelta : NNReal} {iota : Type} {coarseCard : Nat}
    [Fintype iota] [DecidableEq iota]
    {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
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
    (hCFBudget :
      (exactUniformCoarseKatzTaoNNReal sourceA Ppart : ENNReal) * 512 <=
        (globalDelta : ENNReal) ^
            (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
              P j) *
          ((exactPartitionStickyCover Ppart).activeCoarse.card : ENNReal) *
          ((b : ENNReal) ^ 2 / 2))
    (hglobalSmall : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j)
    (hsourceKT : IsKatzTao (sourceA : ENNReal) D.family.bodyFamily)
    (hAKT : 1024 * exactUniformCoarseKatzTaoNNReal sourceA Ppart <=
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
    Family8ExactUniformDiscreteLongIntervalBootstrapV1.longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_exactUniformDiscreteEndpoint
      D hD coarse Ppart hloss hcoarse P j sourceA
      hglobal hglobalOne hglobalB hbUpper hbHalf hbeta hgamma
  · exact
      exactPartitionStickyCover_canonicalFrostmanConstant_le_of_cardScaleBudget
        D hD coarse Ppart hloss hcoarse sourceA
        ((globalDelta : ENNReal) ^
          (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
            P j))
        hb hbHalf hsourceKT hCFBudget
  · exact hglobalSmall
  · exact hsourceKT
  · exact hAKT

#print axioms
  exactPartitionStickyCover_canonicalFrostmanConstant_le_of_cardScaleBudget
#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_exactUniformScalarBudgets

end
end Family8ExactUniformDiscreteLongIntervalBootstrapV2
