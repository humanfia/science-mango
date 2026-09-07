import Family8Grounding.Family8CanonicalGraphFrozenActiveParentRecoveryV1
import Family8Grounding.Family8CanonicalGraphFrozenGraphAverageAutomaticRowFactorV1
import Family8Grounding.Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
import Family8Grounding.Family8NormalizedLongCoreGraphPrefixActualEq66V1
import Mathlib.Tactic

/-!
# Exact same-graph Eq. (66) prefix and actual-frozen ledger to DSO

This is the selected-object downstream connector.  The collapsed prefix is
factored through `R.graphAverage` and the H-row selected from that exact
graph.  The frozen-coarse average appears only in the raw Eq. (66) third
factor.  No displayed coefficient or frozen-average-to-row comparison is
present.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenGraphPrefixActualLedgerEq66ToDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8CanonicalGraphFrozenActiveParentRecoveryV1
open Family8CanonicalGraphFrozenGraphAverageAutomaticRowFactorV1
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1.NormalizedLongCoreActualPrefixEq66Inputs
open Family8NormalizedLongCoreGraphPrefixActualEq66V1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66RowAutomaticForwardThickeningConnectorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyParentHullVolumeBoundV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- The literal square-plank datum selected from the graph stored in `R`.
The active-parent proof is recovered from `R`; it is not a caller seam. -/
abbrev SameGraphEq66Row
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {fine : UniformTubeFamily tau fineIndex}
    {U : StickyScaleCover fine rho}
    {Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily}
    {Y : Shading fine.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) :=
  sameAssemblyGraphBufferedPlankDatum R htau hrho hrhoOne htauRho
    (SameAssemblyFullCoefficientGraphIdentity.k_mem_activeCoarse R)

/-- The exact outer coefficient multiplying `R.graphAverage` in the
canonical collapsed prefix. -/
def sameGraphEq66OuterPrefix
    {tau rho delta : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {fine : UniformTubeFamily tau fineIndex}
    {U : StickyScaleCover fine rho}
    {Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily}
    {Y : Shading fine.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    (firstCap : ENNReal) (lossEta : Real) : ENNReal :=
  (firstCap * (4 * (delta : ENNReal) ^ (-lossEta))) * R.graphLoss

/-- Close the long-core DSO at one literal graph identity and one literal
H-row setup.  The graph-prefix record, actual-frozen ledger identification,
third inflation, and terminal connector are all constructed internally. -/
theorem dividingScaleOutput_of_sameGraphHRow_groundedRun_graphPrefix_actualFrozenLedger_rawEq66
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
    (htau : 0 < Sseq.tau W.m)
    (hrho : 0 < canonicalBufferedRadius W)
    (hrhoOne : canonicalBufferedRadius W ≤ 1)
    (htauRho : Sseq.tau W.m ≤ canonicalBufferedRadius W)
    (H : SquarePlankHRowSelectionFirstSetup
      (SameGraphEq66Row R htau hrho hrhoOne htauRho))
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      (SameGraphEq66Row R htau hrho hrhoOne htauRho)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        epsilonRow betaRow etaRow)
    (hepsilonRow : 0 ≤ epsilonRow)
    (hbetaRow0 : 0 ≤ betaRow) (hbetaRow2 : betaRow ≤ 2)
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
    (hOuterFactor :
      sameGraphEq66OuterPrefix (delta := delta) R firstCap lossEta *
        hRowFreshAutomaticForwardProp66Factor
          (SameGraphEq66Row R htau hrho hrhoOne htauRho)
          H.C H.q universalHRowCell universalHRowCell_measurable
          (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
          B (Fintype.card {i // i ∈ sameAssemblyGraph R} : NNReal) H.loss ≤
      residualFirstLedgerLoss run.productLedger R.A *
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
    (hSmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput Dsource P targetEpsilon := by
  let rowFactor := hRowFreshAutomaticForwardProp66Factor
    (SameGraphEq66Row R htau hrho hrhoOne htauRho)
    H.C H.q universalHRowCell universalHRowCell_measurable
    (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
    B (Fintype.card {i // i ∈ sameAssemblyGraph R} : NNReal) H.loss
  have hGraphToFactor : R.graphAverage ≤ rowFactor := by
    simpa only [SameGraphEq66Row, rowFactor] using
      graphAverage_le_sameGraphAutomaticForwardProp66Factor
        R htau hrho hrhoOne htauRho
          (SameAssemblyFullCoefficientGraphIdentity.k_mem_activeCoarse R)
          H B hepsilonRow hbetaRow0 hbetaRow2
  let ledgerId : CorrelatedEq66LedgerIdentification
      run.productLedger delta sourceIndex middleCount
        (Fintype.card (Fin U.coarseCard))
        (residualFirstLedgerLoss run.productLedger R.A)
        (actualFrozenThirdLedgerLoss R.A)
        (cumulativeForwardLoss run.productLedger) :=
    groundedRun_correlatedEq66LedgerIdentification_actualFrozenThird
      Dsource hDsource Cmulti sourceDef212Constant sourceExact R.A run
        middleCount (by simpa using final_cardProduct_eq)
  have hGammaTwo : gamma ≤ 2 := hGammaOne.trans (by norm_num)
  have hCollapsedGraph :
      R.collapsedPrefix (delta := delta) firstCap lossEta ≤
        sameGraphEq66OuterPrefix (delta := delta) R firstCap lossEta *
          R.graphAverage := by
    exact le_of_eq (sameAssembly_collapsedPrefix_eq_graphProduct
      (delta := delta) R firstCap lossEta)
  let Z : NormalizedLongCoreActualPrefixEq66Inputs
      Dsource hDsource Cmulti Sseq P W :=
    groundedRun_normalizedActualPrefixEq66InputsOfGraphFactorSandwich
      Dsource hDsource Cmulti Sseq P W R.graphAverage rowFactor
        hGraphToFactor run hUniformityExp hFreshExp hUniformity hFresh
        (canonicalBufferedRadius W) middleCount
        (Fintype.card (Fin U.coarseCard))
        (R.collapsedPrefix (delta := delta) firstCap lossEta)
        (sameGraphEq66OuterPrefix (delta := delta) R firstCap lossEta)
        (residualFirstLedgerLoss run.productLedger R.A)
        (actualFrozenThirdLedgerLoss R.A)
        (cumulativeForwardLoss run.productLedger) ledgerId hGammaTwo
        hCollapsedGraph (by simpa only [rowFactor] using hOuterFactor)
        hExponentBudget
  have hTriple : Dsource.shading.averageMultiplicity ≤
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
    apply hTriple_of_graphPrefix_rawEq66
      Dsource hDsource Cmulti Sseq P W fine U Y Q R.A Z Aouter hbeta
        hGammaOne hepsilonHalf hrhoHalf hfine hC htauSmall hKTEvery hAKT
    · rfl
    · change Fintype.card (Fin U.coarseCard) = U.coarseCard
      exact Fintype.card_fin _
    · exact hGlobalCoarseCard
    · exact actualFrozenAverage_le_actualFrozenThirdLedgerLoss R.A
    · change Dsource.shading.averageMultiplicity ≤
        R.collapsedPrefix (delta := delta) firstCap lossEta *
          R.A.frozenCoarse.averageMultiplicity
      exact hRawEq66
  have hTauMiddle : Sseq.tau W.m ≤ Z.middleScale := by
    change Sseq.tau W.m ≤ canonicalBufferedRadius W
    exact htauRho
  exact Z.toDividingScaleOutput Dsource hDsource Cmulti Sseq P W
    hTauMiddle hGammaOne hTriple hSmall hTargetEpsilon

#print axioms SameGraphEq66Row
#print axioms sameGraphEq66OuterPrefix
#print axioms
  dividingScaleOutput_of_sameGraphHRow_groundedRun_graphPrefix_actualFrozenLedger_rawEq66

end
end Family8CanonicalGraphFrozenGraphPrefixActualLedgerEq66ToDSOV1
