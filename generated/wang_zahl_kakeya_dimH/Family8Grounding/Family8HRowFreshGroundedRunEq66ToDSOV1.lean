import Family8Grounding.Family8HRowFreshSameObjectEq66TripleProducerV1
import Family8Grounding.Family8NormalizedLongCoreCorrelatedEq66ToDSOV1
import Mathlib.Tactic

/-!
# Grounded HRow-fresh run through Equation (66) to the dividing-scale output

This connector calls the existing grounded-run producer exactly once.  Its
count and aggregate-loss fields therefore come from the literal repeated
ledger.  The resulting record is passed, without reconstruction, through the
same-object raw-Equation-(66) triple producer and then into the established
normalized LongCore DSO consumer.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowFreshGroundedRunEq66ToDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1
open Family8HRowFreshSameObjectEq66TripleProducerV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
open Family8NormalizedLongCoreCorrelatedEq66ToDSOV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorFiniteRunPowerEnvelopeV1
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SameObjectCorrelatedSelectedThirdCertificateV1
open Family8StickyParentHullVolumeBoundV1
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

/-- End-to-end positive connector.  `hRawEq66` is the earliest geometric
source-to-frozen-average inequality and `hThirdLoss` is the same-assembly
loss allocation.  In particular `hCount`, `hAggregateLoss`, `hPrefix`, and
the terminal `hTriple` are all produced internally. -/
theorem dividingScaleOutput_of_groundedRun_hRowFresh_rawEq66
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
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
    (selectedThird : SameObjectCorrelatedSelectedThirdCertificate
      (delta := delta) U Y Q A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p))
    (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real} (M : NNReal)
    (correlationLoss : ENNReal)
    (Z : Prop66Eq66ComposerFromHRowFresh
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow M
        A.frozenCoarse.averageMultiplicity correlationLoss)
    (hCoefficientToRow : HRowFreshCorrelatedCoefficientToRowFactor
      (delta := delta) X selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M)
    {runN sourceStage finalStage : Nat}
    {sourceState finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      sourceState finalState)
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
    (hThirdCount : thirdCount = Fintype.card coarseIndex)
    (collapsedPrefix outerPrefix firstLoss thirdLoss countLoss : ENNReal)
    (ledgerId : CorrelatedEq66LedgerIdentification
      run.productLedger delta sourceIndex middleCount thirdCount
        firstLoss thirdLoss countLoss)
    (hCollapsed : collapsedPrefix ≤
      outerPrefix * A.frozenCoarse.averageMultiplicity)
    (hOuterRowFactor : outerPrefix *
        hRowFreshProp66Factor
          Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma)
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
    (hMiddleScale : middleScale = canonicalBufferedRadius W)
    (hCoarseCard : U.coarseCard =
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card)
    (hThirdLoss : A.frozenCoarse.averageMultiplicity ≤ thirdLoss)
    (hRawEq66 : Dsource.shading.averageMultiplicity ≤
      collapsedPrefix * A.frozenCoarse.averageMultiplicity)
    (hSmall : delta ≤
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput Dsource P targetEpsilon := by
  have hGammaTwo : gamma ≤ 2 := hGammaOne.trans (by norm_num)
  let R := groundedRun_normalizedCorrelatedEq66InputsOfHRowFresh
    Dsource hDsource Cmulti Sseq P W fine G U Y Q A
      X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
        densityRetentionLoss outputEta selectedThird
      Drow Crow q cell hcell selectedCells hmass hactive M correlationLoss Z
      hCoefficientToRow run hUniformityExp hFreshExp hUniformity hFresh
      middleScale middleCount thirdCount hThirdCount collapsedPrefix
      outerPrefix firstLoss thirdLoss countLoss ledgerId hGammaTwo hCollapsed
      hOuterRowFactor hExponentBudget
  have hMiddleScaleR : R.1.middleScale = canonicalBufferedRadius W := by
    change middleScale = canonicalBufferedRadius W
    exact hMiddleScale
  have hThirdLossR : A.frozenCoarse.averageMultiplicity ≤ R.1.thirdLoss := by
    change A.frozenCoarse.averageMultiplicity ≤ thirdLoss
    exact hThirdLoss
  have hRawEq66R : Dsource.shading.averageMultiplicity ≤
      R.1.collapsedPrefix * A.frozenCoarse.averageMultiplicity := by
    change Dsource.shading.averageMultiplicity ≤
      collapsedPrefix * A.frozenCoarse.averageMultiplicity
    exact hRawEq66
  have hTriple := hTriple_of_sameObject_rawEq66
    Dsource hDsource Cmulti Sseq P W fine G U Y Q A
      X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
        densityRetentionLoss outputEta R.1 Aouter hbeta hGammaOne
      hepsilonHalf hrhoHalf hfine hC htauSmall hKTEvery hAKT
      hMiddleScaleR hCoarseCard hThirdLossR hRawEq66R
  have hTauMiddle : Sseq.tau W.m ≤ R.1.middleScale := by
    rw [hMiddleScaleR]
    exact tau_le_canonicalBufferedRadius W hDsource.delta_pos P.epsilon_pos.le
  exact
    Family8NormalizedLongCoreCorrelatedEq66ToDSOV1.NormalizedLongCoreCorrelatedEq66Inputs.toDividingScaleOutput
    Dsource hDsource Cmulti Sseq P W fine G U Y Q A
      X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
        densityRetentionLoss outputEta R.1 hTauMiddle hGammaOne hTriple hSmall
          hTargetEpsilon

#print axioms dividingScaleOutput_of_groundedRun_hRowFresh_rawEq66

end
end Family8HRowFreshGroundedRunEq66ToDSOV1
