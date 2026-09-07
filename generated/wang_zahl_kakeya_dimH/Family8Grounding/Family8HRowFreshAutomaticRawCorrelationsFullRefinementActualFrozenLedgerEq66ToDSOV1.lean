import Family8Grounding.Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
import Family8Grounding.Family8ActualThirdSelectedCoefficientFromFrozenComparableV1
import Family8Grounding.Family8HRowDisplayedCoefficientIncidenceFromMassFloorV1
import Family8Grounding.Family8HRowFreshSameObjectEq66TripleProducerV1
import Family8Grounding.Family8NormalizedLongCoreCorrelatedEq66ToDSOV1
import Family8Grounding.Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
import Mathlib.Tactic

/-!
# Raw-correlation HRow E2E with the actual frozen ledger

This variant combines the consumer-facing raw-correlation Prop. 6.6
connector with the canonical actual-frozen-third ledger allocation.  It does
not use either direction of the obsolete factor sandwich.  The only HRow
coefficient assumptions are the two literal inequalities used downstream:

* the actual frozen average lies below the selected coefficient;
* the displayed correlated coefficient lies below the same-row average with
  its explicit correlation loss.

The full-refinement source state, forward/reverse losses, third loss, count
loss, and ledger identification are all generated internally.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowFreshAutomaticRawCorrelationsFullRefinementActualFrozenLedgerEq66ToDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
open Family8ActualThirdSelectedCoefficientFromFrozenComparableV1
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8HRowFreshSameObjectEq66TripleProducerV1
open Family8HRowDisplayedCoefficientIncidenceFromMassFloorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
open Family8NormalizedLongCoreCorrelatedEq66ToDSOV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
open Family8Prop66RowAutomaticForwardThickeningConnectorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
variable {a b : NNReal}

/-- Full Eq. (66)-to-DSO connector at the literal raw HRow correlation
directions and the actual frozen-third ledger allocation. -/
theorem dividingScaleOutput_of_fullRefinementGroundedRun_hRowFreshAutomaticRawCorrelations_actualFrozenLedger_rawEq66
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base sourceDef212Constant)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti P.N P.epsilon P.eta Sseq)
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    (fine : UniformTubeFamily (Sseq.tau W.m) fineIndex)
    (G : ConvexFamily coarseIndex)
    (U : StickyScaleCover fine (canonicalBufferedRadius W))
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal)
    (outputEta : Real)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex -> Set Space)
    (hcell : forall p, MeasurableSet (cell p))
    (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl Drow M)
    (correlationLoss : ENNReal) (hcorrelationTop : correlationLoss ≠ ∞)
    (hFrozenBase : FrozenComparableSelectedCoefficientBaseBudget
      Y Q A CKT selectorLoss)
    (hDisplayed : HRowFreshDisplayedCoefficientRowCorrelation
      (delta := delta) X selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B correlationLoss)
    (hbHalf : b <= (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a <= b)
    (hepsilonRow : 0 <= epsilonRow)
    (hbetaRow0 : 0 <= betaRow) (hbetaRow2 : betaRow <= 2)
    (hSelectedCoarseCard : Fintype.card coarseIndex = U.coarseCard)
    (hSelectedCoarsePos : 0 < Fintype.card coarseIndex)
    (hCardScaleMass : X = (Fintype.card coarseIndex : ENNReal) *
      ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (2 : Nat))
    (hCoefficientCardScale :
      CKT * volume (unitBallBody : Set Space) <=
        128 * (delta : ENNReal) ^ (-outputEta) * X)
    (hFourthCardScale :
      ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (4 : Nat) * X <= 1)
    (hSourceMass : sourceMass <=
      massRetentionLoss * shadingMassOn Y U.activeFine)
    (hSourceDensity : densityRetentionLoss * sourceDensity <=
      Y.shadingDensity)
    {runN sourceStage finalStage : Nat}
    {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState Dsource hDsource
        Cmulti sourceDef212Constant sourceExact) finalState)
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
          (-freshExp))
    (middleScale : NNReal) (middleCount : Nat)
    (final_cardProduct_eq : factorCardProduct finalState.factors =
      ((middleCount * Fintype.card coarseIndex : Nat) : ENNReal))
    (collapsedPrefix outerPrefix : ENNReal)
    (hCollapsed : collapsedPrefix <=
      outerPrefix * A.frozenCoarse.averageMultiplicity)
    (hOuterFactor : outerPrefix *
        hRowFreshAutomaticForwardProp66Factor
          Drow Crow q cell hcell selectedCells hmass hactive B M
            correlationLoss <=
      residualFirstLedgerLoss run.productLedger A *
        sectionEightScaleCountFrostmanFactor
          delta middleScale middleCount gamma)
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) <=
        3 * P.eta W.stage)
    (Aouter : NNReal)
    (hbeta : 0 < beta) (hGammaOne : gamma <= 1)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹)
    (hfine : (fullRefinementDatum Dsource).family.refinement.refined.Nonempty)
    (hC : canonicalFrostmanConstant
        (canonicalBufferedGlobalCover W hDsource.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
        closedBallFourBody <=
      (Sseq.tau W.m : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P W.stage))
    (htauSmall : Sseq.tau W.m <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P W.stage)
    (hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale (Aouter : ENNReal))
    (hAKT : 1024 * Aouter <=
      Sseq.tau W.m ^
        (-longIntervalDeltaLoss P.epsilon
          (10 * P.eta W.stage / (P.epsilon * beta))))
    (hMiddleScale : middleScale = canonicalBufferedRadius W)
    (hGlobalCoarseCard : U.coarseCard =
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card)
    (hRawEq66 : Dsource.shading.averageMultiplicity <=
      collapsedPrefix * A.frozenCoarse.averageMultiplicity)
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput Dsource P targetEpsilon := by
  have hGammaTwo : gamma <= 2 := hGammaOne.trans (by norm_num)
  have hActualSelected : HRowFreshActualThirdSelectedCoefficientIncidence
      Y Q A CKT selectorLoss
      Drow Crow q cell hcell selectedCells hmass hactive B :=
    hRowFreshActualThirdSelectedCoefficientIncidence_of_frozenComparableBase
      Y Q A CKT selectorLoss Drow Crow q cell hcell selectedCells
        hmass hactive B hFrozenBase


  let ledgerId : CorrelatedEq66LedgerIdentification
      run.productLedger delta sourceIndex middleCount
        (Fintype.card coarseIndex)
        (residualFirstLedgerLoss run.productLedger A)
        (actualFrozenThirdLedgerLoss A)
        (cumulativeForwardLoss run.productLedger) :=
    groundedRun_correlatedEq66LedgerIdentification_actualFrozenThird
      Dsource hDsource Cmulti sourceDef212Constant sourceExact A run
        middleCount final_cardProduct_eq
  let R :=
    groundedRun_normalizedCorrelatedEq66InputsOfHRowFreshAutomaticRawCorrelations
      Dsource hDsource Cmulti Sseq P W fine G U Y Q A
        X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
          densityRetentionLoss outputEta
        Drow Crow q cell hcell selectedCells hmass hactive B M hthick
          correlationLoss hcorrelationTop hActualSelected hDisplayed hbHalf
          ha hab hepsilonRow hbetaRow0 hbetaRow2
          hSelectedCoarseCard hSelectedCoarsePos hCardScaleMass
          hCoefficientCardScale hFourthCardScale hSourceMass hSourceDensity
          run hUniformityExp hFreshExp hUniformity hFresh middleScale
          middleCount (Fintype.card coarseIndex) rfl collapsedPrefix
          outerPrefix (residualFirstLedgerLoss run.productLedger A)
          (actualFrozenThirdLedgerLoss A)
          (cumulativeForwardLoss run.productLedger) ledgerId hGammaTwo
          hCollapsed hOuterFactor hExponentBudget
  have hMiddleScaleR : R.1.middleScale = canonicalBufferedRadius W := by
    change middleScale = canonicalBufferedRadius W
    exact hMiddleScale
  have hThirdLossR : A.frozenCoarse.averageMultiplicity <= R.1.thirdLoss := by
    change A.frozenCoarse.averageMultiplicity <= actualFrozenThirdLedgerLoss A
    exact actualFrozenAverage_le_actualFrozenThirdLedgerLoss A
  have hRawEq66R : Dsource.shading.averageMultiplicity <=
      R.1.collapsedPrefix * A.frozenCoarse.averageMultiplicity := by
    change Dsource.shading.averageMultiplicity <=
      collapsedPrefix * A.frozenCoarse.averageMultiplicity
    exact hRawEq66
  have hTriple := hTriple_of_sameObject_rawEq66
    Dsource hDsource Cmulti Sseq P W fine G U Y Q A
      X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
        densityRetentionLoss outputEta R.1 Aouter hbeta hGammaOne
      hepsilonHalf hrhoHalf hfine hC htauSmall hKTEvery hAKT
      hMiddleScaleR hGlobalCoarseCard hThirdLossR hRawEq66R
  have hTauMiddle : Sseq.tau W.m <= R.1.middleScale := by
    rw [hMiddleScaleR]
    exact tau_le_canonicalBufferedRadius W
      hDsource.delta_pos P.epsilon_pos.le
  exact
    NormalizedLongCoreCorrelatedEq66Inputs.toDividingScaleOutput
      Dsource hDsource Cmulti Sseq P W fine G U Y Q A
        X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
          densityRetentionLoss outputEta R.1 hTauMiddle hGammaOne
            hTriple hSmall hTargetEpsilon

#print axioms
  dividingScaleOutput_of_fullRefinementGroundedRun_hRowFreshAutomaticRawCorrelations_actualFrozenLedger_rawEq66

end
end Family8HRowFreshAutomaticRawCorrelationsFullRefinementActualFrozenLedgerEq66ToDSOV1
