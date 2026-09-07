import Family8Grounding.Family8CanonicalGraphFrozenActiveParentRecoveryV1
import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
import Family8Grounding.Family8NormalizedLongCoreGraphPrefixActualEq66V1
import Family8Grounding.Family8PaperFactorFiniteRunPowerEnvelopeV1
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Mathlib.Tactic

/-!
# Full raw-prefix allocation to the reverse ledger

The terminal Equation-(66) consumer does not require the frozen-coarse
average to be isolated as a third ledger loss.  This module keeps the whole
raw product

`collapsedPrefix * frozenCoarse.averageMultiplicity`

as the actual prefix, assigns the complete reverse ledger to the first loss,
and assigns `1` to the third loss.  Thus the only scalar allocation premise is
the direct payment of that full raw prefix by the reverse ledger and the
Section-8 middle factor.

This is a conditional terminal interface.  In particular it does not claim
to produce the direct payment or the final factor-cardinality decomposition.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenFullRawPrefixReverseLedgerEq66ToDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8CanonicalGraphFrozenActiveParentRecoveryV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1.NormalizedLongCoreActualPrefixEq66Inputs
open Family8NormalizedLongCoreEq66FactorOneV2
open Family8NormalizedLongCoreGraphPrefixActualEq66V1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunPowerEnvelopeV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8StickyParentHullVolumeBoundV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-! ## Minimal reverse-ledger allocation -/

/-- Build the actual-prefix terminal record after assigning the complete
reverse ledger to the first loss and `1` to the third loss. -/
def groundedRun_normalizedActualPrefixEq66InputsOfFullReverseAllocation
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs Cmulti.base sourceDef212Constant)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti P.N P.epsilon P.eta Sseq)
    {runN sourceStage finalStage : Nat} {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState Dsource hDsource
        Cmulti sourceDef212Constant sourceExact) finalState)
    {uniformityExp freshExp : Real}
    (hUniformityExp : 0 ≤ uniformityExp)
    (hFreshExp : 0 ≤ freshExp)
    (hUniformity : ∀ step, step ∈ run.productLedger.steps →
      step.uniformityLoss ≤
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp))
    (hFresh : ∀ step, step ∈ run.productLedger.steps →
      step.freshRetentionLoss ≤
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-freshExp))
    (middleScale : NNReal) (middleCount thirdCount : Nat)
    (final_cardProduct_eq : factorCardProduct finalState.factors =
      ((middleCount * thirdCount : Nat) : ENNReal))
    (fullRawPrefix : ENNReal)
    (hPrefix : fullRawPrefix ≤
      cumulativeReverseLoss run.productLedger *
        sectionEightScaleCountFrostmanFactor
          delta middleScale middleCount gamma)
    (hGammaTwo : gamma ≤ 2)
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) ≤
        3 * P.eta W.stage) :
    NormalizedLongCoreActualPrefixEq66Inputs
      Dsource hDsource Cmulti Sseq P W := by
  let firstLedgerLoss := cumulativeReverseLoss run.productLedger
  let thirdLedgerLoss : ENNReal := 1
  let countLedgerLoss := cumulativeForwardLoss run.productLedger
  let ledgerId : CorrelatedEq66LedgerIdentification
      run.productLedger delta sourceIndex middleCount thirdCount
        firstLedgerLoss thirdLedgerLoss countLedgerLoss :=
    groundedRun_correlatedEq66LedgerIdentification_of_fullRefinementState
      Dsource hDsource Cmulti sourceDef212Constant sourceExact run
        middleCount thirdCount firstLedgerLoss thirdLedgerLoss
          final_cardProduct_eq (by
            simp only [firstLedgerLoss, thirdLedgerLoss, mul_one]
            exact le_rfl)
  have hPowers :=
    power_envelopes_of_groundedPaperFactorFiniteRun_uniformLocalBudget
      run hUniformityExp hFreshExp hUniformity hFresh
  have hCountAggregate :=
    count_and_aggregate_fields_of_repeatedBadParentLedger
      Dsource hDsource Cmulti Sseq P W run.productLedger
        middleCount thirdCount firstLedgerLoss thirdLedgerLoss
          countLedgerLoss ledgerId hGammaTwo hPowers.1 hPowers.2
            hExponentBudget
  exact
    { middleScale := middleScale
      middleCount := middleCount
      thirdCount := thirdCount
      collapsedPrefix := fullRawPrefix
      firstLoss := firstLedgerLoss
      thirdLoss := thirdLedgerLoss
      countLoss := countLedgerLoss
      actualPrefixBudget := by
        simpa only [firstLedgerLoss] using hPrefix
      hCount := hCountAggregate.1
      hAggregateLoss := hCountAggregate.2 }

/-! ## Triple inflation with unit third loss -/

/-- Inflate a full raw prefix by the canonical Equation-(66) factor.  Since
the frozen average is already inside the prefix, the terminal third loss is
exactly `1`. -/
theorem hTriple_of_fullRawPrefix_thirdLossOne
    (D : ActualTubeDatum delta sourceIndex) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (Z : NormalizedLongCoreActualPrefixEq66Inputs D hD C S P W)
    (Aouter : NNReal)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹)
    (hfine : (fullRefinementDatum D).family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody ≤
      (S.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : S.tau W.m ≤
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hKTEvery : C.base.IsKatzTaoAtEveryScale (Aouter : ENNReal))
    (hAKT : 1024 * Aouter ≤
      S.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta))))
    (hMiddleScale : Z.middleScale = canonicalBufferedRadius W)
    (hThirdCount : Z.thirdCount =
      (canonicalBufferedGlobalCover W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card)
    (hThirdLoss : Z.thirdLoss = 1)
    (hRawPrefix : D.shading.averageMultiplicity ≤ Z.collapsedPrefix) :
    D.shading.averageMultiplicity ≤
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  have hFactorOne : (1 : ENNReal) ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          Z.middleScale 1 Z.thirdCount gamma := by
    rw [hMiddleScale, hThirdCount]
    exact one_le_canonicalBufferedGlobal_eq66Factor
      E hE C S P W Aouter hbeta hgamma hepsilonHalf hrhoHalf
        hfine hC htauSmall hKTEvery hAKT
  have hInflatedOne : (1 : ENNReal) ≤
      ((delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss := by
    rw [hThirdLoss, mul_one]
    exact hFactorOne
  calc
    D.shading.averageMultiplicity ≤ Z.collapsedPrefix := hRawPrefix
    _ = Z.collapsedPrefix * 1 := by rw [mul_one]
    _ ≤ Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) :=
      mul_le_mul' le_rfl hInflatedOne

/-! ## Canonical same-assembly specialization -/

/-- Close the long-core DSO from one full raw-prefix payment.  No H-row,
displayed coefficient, or separate frozen-third ledger allocation appears in
the interface. -/
theorem dividingScaleOutput_of_sameAssemblyFullRawPrefix_reverseLedger_rawEq66
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs Cmulti.base sourceDef212Constant)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti P.N P.epsilon P.eta Sseq)
    {fineIndex : Type} [Fintype fineIndex] [DecidableEq fineIndex]
    (fine : UniformTubeFamily (Sseq.tau W.m) fineIndex)
    (U : StickyScaleCover fine (canonicalBufferedRadius W))
    (Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily)
    (Y : Shading fine.bodyFamily) (fibreCF : ENNReal)
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    {runN sourceStage finalStage : Nat} {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState Dsource hDsource
        Cmulti sourceDef212Constant sourceExact) finalState)
    {uniformityExp freshExp : Real}
    (hUniformityExp : 0 ≤ uniformityExp)
    (hFreshExp : 0 ≤ freshExp)
    (hUniformity : ∀ step, step ∈ run.productLedger.steps →
      step.uniformityLoss ≤
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-uniformityExp))
    (hFresh : ∀ step, step ∈ run.productLedger.steps →
      step.freshRetentionLoss ≤
        ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
          (-freshExp))
    (middleCount : Nat)
    (final_cardProduct_eq : factorCardProduct finalState.factors =
      ((middleCount * U.coarseCard : Nat) : ENNReal))
    (firstCap : ENNReal) (lossEta : Real)
    (hFullRawPrefix :
      R.collapsedPrefix (delta := delta) firstCap lossEta *
          R.A.frozenCoarse.averageMultiplicity ≤
        cumulativeReverseLoss run.productLedger *
          sectionEightScaleCountFrostmanFactor
            delta (canonicalBufferedRadius W) middleCount gamma)
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) ≤
        3 * P.eta W.stage)
    (Aouter : NNReal)
    (hbeta : 0 < beta) (hGammaOne : gamma ≤ 1)
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W ≤ (2 : NNReal)⁻¹)
    (hfine : (fullRefinementDatum Dsource).family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover W hDsource.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody ≤
      (Sseq.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : Sseq.tau W.m ≤
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale (Aouter : ENNReal))
    (hAKT : 1024 * Aouter ≤
      Sseq.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta))))
    (hGlobalCoarseCard : U.coarseCard =
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card)
    (hRawEq66 : Dsource.shading.averageMultiplicity ≤
      R.collapsedPrefix (delta := delta) firstCap lossEta *
        R.A.frozenCoarse.averageMultiplicity)
    (hTauMiddle : Sseq.tau W.m ≤ canonicalBufferedRadius W)
    (hSmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput Dsource P targetEpsilon := by
  have hGammaTwo : gamma ≤ 2 := hGammaOne.trans (by norm_num)
  let Z : NormalizedLongCoreActualPrefixEq66Inputs
      Dsource hDsource Cmulti Sseq P W :=
    groundedRun_normalizedActualPrefixEq66InputsOfFullReverseAllocation
      Dsource hDsource Cmulti sourceDef212Constant sourceExact Sseq P W run
        hUniformityExp hFreshExp hUniformity hFresh
        (canonicalBufferedRadius W) middleCount
        (Fintype.card (Fin U.coarseCard)) (by
          simpa using final_cardProduct_eq)
        (R.collapsedPrefix (delta := delta) firstCap lossEta *
          R.A.frozenCoarse.averageMultiplicity)
        hFullRawPrefix hGammaTwo hExponentBudget
  have hTriple : Dsource.shading.averageMultiplicity ≤
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
    apply hTriple_of_fullRawPrefix_thirdLossOne
      Dsource hDsource Cmulti Sseq P W Z Aouter hbeta hGammaOne
        hepsilonHalf hrhoHalf hfine hC htauSmall hKTEvery hAKT
    · rfl
    · change Fintype.card (Fin U.coarseCard) =
        (canonicalBufferedGlobalCover W hDsource.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarse.card
      exact (Fintype.card_fin U.coarseCard).trans hGlobalCoarseCard
    · rfl
    · change Dsource.shading.averageMultiplicity ≤
        R.collapsedPrefix (delta := delta) firstCap lossEta *
          R.A.frozenCoarse.averageMultiplicity
      exact hRawEq66
  exact Z.toDividingScaleOutput Dsource hDsource Cmulti Sseq P W
    hTauMiddle hGammaOne hTriple hSmall hTargetEpsilon

#print axioms
  groundedRun_normalizedActualPrefixEq66InputsOfFullReverseAllocation
#print axioms hTriple_of_fullRawPrefix_thirdLossOne
#print axioms
  dividingScaleOutput_of_sameAssemblyFullRawPrefix_reverseLedger_rawEq66

end
end Family8CanonicalGraphFrozenFullRawPrefixReverseLedgerEq66ToDSOV1
