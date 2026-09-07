import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Family8Grounding.Family8ActualThirdSelectedCoefficientFromFrozenComparableV1
import Family8Grounding.Family8HRowDisplayedCoefficientIncidenceFromMassFloorV1
import Family8Grounding.Family8HRowFreshAutomaticRawCorrelationsFullRefinementActualFrozenLedgerEq66ToDSOV1
import Mathlib.Tactic

/-!
# Selection-first canonical graph/frozen actual-ledger DSO closure

The canonical graph producer existentially selects one frozen assembly.  A
downstream theorem must therefore consume that literal assembly rather than
selecting another assembly and postulating an equality.  This module first
selects the graph identity `R`, then proves the complete downstream closure
at `R.A` using the raw Equation-(66) inequality returned with `R`.

The exported closure has no raw-Eq66 input, no third-loss input, and no
ledger-identification input.  It retains the two earliest HRow raw
correlations and the final scalar factor-card decomposition.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ActualThirdSelectedCoefficientFromFrozenComparableV1
open Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8FullRefinementActualDatumV1
open Family8HRowFreshAutomaticRawCorrelationsFullRefinementActualFrozenLedgerEq66ToDSOV1
open Family8HRowDisplayedCoefficientIncidenceFromMassFloorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
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
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickySourceMassFactorizationRoundTripV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

set_option linter.unusedVariables false
/-- All downstream obligations at one already-selected graph/frozen
identity.  The raw graph/frozen product is deliberately absent: it is
supplied by the selection theorem below. -/
def SameAssemblyGraphFrozenActualLedgerDSOClosure
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
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
    (collapsedPrefix : ENNReal) : Prop :=
  forall
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base sourceDef212Constant)
    (X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal)
    (outputEta : Real)
    (rowIndex : Type) [_rowFintype : Fintype rowIndex]
    [_rowDecidableEq : DecidableEq rowIndex]
    (a b : NNReal)
    (Drow : ShadedConvexPlankFamily rowIndex a b)
    (theta : NNReal)
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    (cellIndex : Type v) (cell : cellIndex -> Set Space)
    (hcell : forall p, MeasurableSet (cell p))
    (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    (epsilonRow betaRow etaRow : Real)
    (B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl Drow M)
    (correlationLoss : ENNReal) (hcorrelationTop : correlationLoss ≠ ∞)
    (hFrozenBase : FrozenComparableSelectedCoefficientBaseBudget
      Y Q R.A CKT selectorLoss)
    (hDisplayedToGraph :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) <=
        R.graphAverage)
    (hGraphToSameRow : R.graphAverage <= correlationLoss *
      (HRowFreshPlankDatum
        Drow Crow q cell hcell selectedCells hmass hactive
          B.tau B.S).shading.averageMultiplicity)
    (hbHalf : b <= (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a <= b)
    (hepsilonRow : 0 <= epsilonRow)
    (hbetaRow0 : 0 <= betaRow) (hbetaRow2 : betaRow <= 2)
    (hSelectedCoarsePos : 0 < U.coarseCard)
    (hCardScaleMass : X = (U.coarseCard : ENNReal) *
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
    (runN sourceStage finalStage : Nat)
    (finalState : PaperFactorState)
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState Dsource hDsource
        Cmulti sourceDef212Constant sourceExact) finalState)
    (uniformityExp freshExp : Real)
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
      ((middleCount * U.coarseCard : Nat) : ENNReal))
    (outerPrefix : ENNReal)
    (hCollapsed : collapsedPrefix <=
      outerPrefix * R.A.frozenCoarse.averageMultiplicity)
    (hOuterFactor : outerPrefix *
        hRowFreshAutomaticForwardProp66Factor
          Drow Crow q cell hcell selectedCells hmass hactive B M
            correlationLoss <=
      residualFirstLedgerLoss run.productLedger R.A *
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
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon),
    DividingScaleOutput Dsource P targetEpsilon
set_option linter.unusedVariables true

/-- Select the canonical graph/frozen identity first, and close the entire
downstream actual-ledger implication at that exact selected assembly.

The raw Eq. (66) product returned by the selector is consumed inside the
proof and is absent from the exported closure. -/
theorem exists_canonicalGraphFrozenIdentity_with_actualLedgerDSOClosure
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <=
      (1 / 16 : NNReal))
    (fibreCF : ENNReal) (hCFfinite : fibreCF ≠ ∞)
    (hFibres :
      let E := fullRefinementDatum Dsource
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hDsource
      let U0 := canonicalBufferedTauActiveCover E hE Cmulti Sseq W
        P.epsilon_pos.le hepsilonHalf
      (activeFineRestrictedScaleCover U0).IsFrostmanAtScale fibreCF)
    {etaF etaKT lossEta : Real}
    (hFsource : FrostmanHypotheses Dsource etaF)
    (hKTsource : KatzTaoHypotheses Dsource etaKT)
    (hlossEta : 0 < lossEta)
    (hdeltaLoss : delta <=
      Family8ActiveFrozenComparableLogLossAbsorptionV4.activeFrozenComparableLossAbsorptionThreshold
        lossEta) :
    let E := fullRefinementDatum Dsource
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hDsource
    let U0 := canonicalBufferedTauActiveCover E hE Cmulti Sseq W
      P.epsilon_pos.le hepsilonHalf
    let hscale : Sseq.tau W.m <= canonicalBufferedRadius W :=
      tau_le_canonicalBufferedRadius W hDsource.delta_pos P.epsilon_pos.le
    let Y0 := (tauActiveCoarseDatum E Cmulti Sseq W).shading
    let hsource :
        (IndexedShadingRefinement.restrictTo Y0
          U0.activeFine).shading.shadingMass ≠ 0 := by
      have hmass : Dsource.shading.shadingMass ≠ 0 := by
        have hfloor : (delta : ENNReal) ^ (2 * etaF) <=
            Dsource.shading.shadingMass :=
          delta_rpow_two_eta_le_shadingMass_of_frostman
            Dsource hDsource hFsource
        have hpositive : 0 < (delta : ENNReal) ^ (2 * etaF) :=
          ENNReal.rpow_pos (ENNReal.coe_pos.mpr hDsource.delta_pos)
            ENNReal.coe_ne_top
        exact ne_of_gt (hpositive.trans_le hfloor)
      exact canonicalBufferedTauActiveCover_restrictedMass_ne_zero
        E hE Cmulti Sseq P W hepsilonHalf
          (Family8IdentifiedDividingWitnessSourceTauFrozenProductV3.Witness.fullRefinement_sourceTau_activeMass_ne_zero
            Dsource Cmulti Sseq W.m hmass)
    let T := activeFineRestrictedScaleCover U0
    let YR := activeFineRestrictedShading U0 Y0
    let hsourceR := activeFineRestrictedSourceMass_ne_zero U0 Y0 hsource
    let Psource := sourceMassCoarseTubePartition T hscale YR hsourceR
    let firstCap : ENNReal :=
      Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (Sseq.tau W.m) ((delta : ENNReal) ^ (-etaKT))
    exists R : SameAssemblyFullCoefficientGraphIdentity
        (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
          fibreCF,
      R.A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U0.activeCoarse.card) /\
      SameAssemblyGraphFrozenActualLedgerDSOClosure
        (targetEpsilon := targetEpsilon)
        Dsource hDsource Cmulti Sseq P W
        (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
        fibreCF R (R.collapsedPrefix (delta := delta) firstCap lossEta) := by
  dsimp only
  obtain ⟨R, hLoss, hRaw⟩ :=
    exists_canonicalGraphFrozenIdentity_rawEq66
      Dsource hDsource Cmulti Sseq P W hepsilonHalf hbufferedSixteenth
        fibreCF hCFfinite hFibres hFsource hKTsource hlossEta hdeltaLoss
  refine ⟨R, hLoss, ?_⟩
  unfold SameAssemblyGraphFrozenActualLedgerDSOClosure
  intro sourceDef212Constant sourceExact
    X CKT selectorLoss sourceMass sourceDensity
    massRetentionLoss densityRetentionLoss outputEta
    rowIndex rowFintype rowDecidableEq a b Drow theta Crow q
    cellIndex cell hcell selectedCells hmass hactive
    epsilonRow betaRow etaRow B M hthick correlationLoss hcorrelationTop
    hFrozenBase hDisplayedToGraph hGraphToSameRow hbHalf ha hab hepsilonRow hbetaRow0 hbetaRow2 hSelectedCoarsePos hCardScaleMass
    hCoefficientCardScale hFourthCardScale hSourceMass hSourceDensity
    runN sourceStage finalStage finalState run uniformityExp freshExp
    hUniformityExp hFreshExp hUniformity hFresh middleScale middleCount
    final_cardProduct_eq outerPrefix hCollapsed hOuterFactor
    hExponentBudget Aouter hbeta hGammaOne hepsilonHalf' hrhoHalf hfine
    hC htauSmall hKTEvery hAKT hMiddleScale hGlobalCoarseCard hSmall
    hTargetEpsilon
  have hDisplayed : HRowFreshDisplayedCoefficientRowCorrelation
      (delta := delta) X selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B correlationLoss := by
    unfold HRowFreshDisplayedCoefficientRowCorrelation
    exact hDisplayedToGraph.trans hGraphToSameRow

  exact
    dividingScaleOutput_of_fullRefinementGroundedRun_hRowFreshAutomaticRawCorrelations_actualFrozenLedger_rawEq66
      Dsource hDsource Cmulti sourceDef212Constant sourceExact Sseq P W
      (activeFineRestrictedFamily (canonicalBufferedTauActiveCover
        (fullRefinementDatum Dsource)
        (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
        P.epsilon_pos.le hepsilonHalf))
      (activeFineRestrictedScaleCover (canonicalBufferedTauActiveCover
        (fullRefinementDatum Dsource)
        (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
        P.epsilon_pos.le hepsilonHalf)).coarse.bodyFamily
      (activeFineRestrictedScaleCover (canonicalBufferedTauActiveCover
        (fullRefinementDatum Dsource)
        (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
        P.epsilon_pos.le hepsilonHalf))
      (activeFineRestrictedShading
        (canonicalBufferedTauActiveCover
          (fullRefinementDatum Dsource)
          (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf)
        (tauActiveCoarseDatum (fullRefinementDatum Dsource)
          Cmulti Sseq W).shading)
      _ R.A X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
      densityRetentionLoss outputEta Drow Crow q cell hcell selectedCells
      hmass hactive B M hthick correlationLoss hcorrelationTop
      hFrozenBase hDisplayed hbHalf ha hab hepsilonRow hbetaRow0
      hbetaRow2 (by simp) (by simpa using hSelectedCoarsePos)
      (by simpa using hCardScaleMass) hCoefficientCardScale hFourthCardScale
      hSourceMass hSourceDensity run hUniformityExp hFreshExp hUniformity
      hFresh middleScale middleCount (by simpa using final_cardProduct_eq)
      (R.collapsedPrefix (delta := delta)
        (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
          delta (Sseq.tau W.m) ((delta : ENNReal) ^ (-etaKT))) lossEta)
      outerPrefix hCollapsed hOuterFactor hExponentBudget Aouter hbeta
      hGammaOne hepsilonHalf' hrhoHalf hfine hC htauSmall hKTEvery hAKT
      hMiddleScale hGlobalCoarseCard hRaw hSmall hTargetEpsilon

#print axioms SameAssemblyGraphFrozenActualLedgerDSOClosure
#print axioms
  exists_canonicalGraphFrozenIdentity_with_actualLedgerDSOClosure

end
end Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
