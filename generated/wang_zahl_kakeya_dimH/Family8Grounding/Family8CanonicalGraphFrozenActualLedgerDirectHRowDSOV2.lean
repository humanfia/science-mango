import Family8Grounding.Family8CanonicalGraphFrozenGraphPrefixActualLedgerEq66ToDSOV1
import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
import Mathlib.Tactic

/-!
# Canonical graph/frozen actual-ledger closure at the literal same-graph H-row

This is the corrected direct-H-row continuation.  The canonical collapsed
prefix is routed through its literal selected graph average:

`collapsedPrefix = graphOuter * R.graphAverage`.

The same graph average is then paid by the H-row selected from that exact
`R`.  The frozen-coarse average occurs only as the third factor in raw
Equation (66); it is never inserted into the collapsed-prefix estimate.

Consequently this module uses the minimal `ActualPrefix` route and does not
pass through the older correlated record or a displayed-coefficient seam.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenActualLedgerDirectHRowDSOV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenGraphPrefixActualLedgerEq66ToDSOV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8FullRefinementActualDatumV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowAutomaticForwardThickeningConnectorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyParentHullVolumeBoundV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

set_option linter.unusedVariables false in
/-- The terminal continuation for one selected graph identity.  The two
potentially error-prone prefix facts are discharged by the downstream
same-graph theorem itself:

* the collapsed prefix is definitionally `graphOuter * R.graphAverage`;
* `R.graphAverage` is controlled by the H-row selected from this same `R`.

The only remaining first/middle scalar premise is `hOuterFactor` below.
Raw Equation (66) is deliberately not a caller premise of this closure; the
canonical selector supplies it in the theorem below. -/
def SameAssemblyGraphFrozenActualLedgerDirectHRowDSOClosure
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
    (firstCap : ENNReal) (lossEta : Real)
    (htau : 0 < Sseq.tau W.m)
    (hrho : 0 < canonicalBufferedRadius W)
    (hrhoOne : canonicalBufferedRadius W <= 1)
    (htauRho : Sseq.tau W.m <= canonicalBufferedRadius W) : Prop :=
  forall
    (sourceDef212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base sourceDef212Constant)
    (H : SquarePlankHRowSelectionFirstSetup
      (SameGraphEq66Row R htau hrho hrhoOne htauRho))
    (epsilonRow betaRow etaRow : Real)
    (B : HRowFreshPropertyBundle
      (SameGraphEq66Row R htau hrho hrhoOne htauRho)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        epsilonRow betaRow etaRow)
    (hepsilonRow : 0 <= epsilonRow)
    (hbetaRow0 : 0 <= betaRow) (hbetaRow2 : betaRow <= 2)
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
    (middleCount : Nat)
    (final_cardProduct_eq : factorCardProduct finalState.factors =
      ((middleCount * U.coarseCard : Nat) : ENNReal))
    (hOuterFactor :
      sameGraphEq66OuterPrefix (delta := delta) R firstCap lossEta *
        hRowFreshAutomaticForwardProp66Factor
          (SameGraphEq66Row R htau hrho hrhoOne htauRho)
          H.C H.q universalHRowCell universalHRowCell_measurable
          (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
          B (Fintype.card {i // i ∈ sameAssemblyGraph R} : NNReal) H.loss <=
      residualFirstLedgerLoss run.productLedger R.A *
        sectionEightScaleCountFrostmanFactor
          delta (canonicalBufferedRadius W) middleCount gamma)
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
    (hGlobalCoarseCard : U.coarseCard =
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card)
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon),
    DividingScaleOutput Dsource P targetEpsilon

/-- Select the canonical graph identity and consume its raw Equation-(66)
inequality internally.  Unlike V1, this theorem enters the `ActualPrefix`
route, so the frozen average is paid exactly once, as the third factor. -/
theorem exists_canonicalGraphFrozenIdentity_with_actualLedgerDirectHRowDSOClosure
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (Sseq : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti P.N P.epsilon P.eta Sseq)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
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
    let htau : 0 < Sseq.tau W.m :=
      hDsource.delta_pos.trans_le (Sseq.delta_le_tau W.m)
    let hrho : 0 < canonicalBufferedRadius W :=
      canonicalBufferedRadius_pos W hDsource.delta_pos P.epsilon_pos.le
    let hrhoOne : canonicalBufferedRadius W <= 1 :=
      canonicalBufferedRadius_le_one W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf
    ∃ R : SameAssemblyFullCoefficientGraphIdentity
        (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
          fibreCF,
      R.A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U0.activeCoarse.card) ∧
      SameAssemblyGraphFrozenActualLedgerDirectHRowDSOClosure
        (targetEpsilon := targetEpsilon)
        Dsource hDsource Cmulti Sseq P W
        (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
        fibreCF R firstCap lossEta htau hrho hrhoOne hscale := by
  dsimp only
  obtain ⟨R, hLoss, hRaw⟩ :=
    exists_canonicalGraphFrozenIdentity_rawEq66
      Dsource hDsource Cmulti Sseq P W hepsilonHalf hbufferedSixteenth
        fibreCF hCFfinite hFibres hFsource hKTsource hlossEta hdeltaLoss
  refine ⟨R, hLoss, ?_⟩
  unfold SameAssemblyGraphFrozenActualLedgerDirectHRowDSOClosure
  intro sourceDef212Constant sourceExact H
    epsilonRow betaRow etaRow B hepsilonRow hbetaRow0 hbetaRow2
    runN sourceStage finalStage finalState run uniformityExp freshExp
    hUniformityExp hFreshExp hUniformity hFresh middleCount
    final_cardProduct_eq hOuterFactor hExponentBudget Aouter hbeta
    hGammaOne hepsilonHalf' hrhoHalf hfine hC htauSmall hKTEvery hAKT
    hGlobalCoarseCard hSmall hTargetEpsilon
  exact
    dividingScaleOutput_of_sameGraphHRow_groundedRun_graphPrefix_actualFrozenLedger_rawEq66
      Dsource hDsource Cmulti sourceDef212Constant sourceExact Sseq P W
      (activeFineRestrictedFamily (canonicalBufferedTauActiveCover
        (fullRefinementDatum Dsource)
        (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
        P.epsilon_pos.le hepsilonHalf))
      (activeFineRestrictedScaleCover (canonicalBufferedTauActiveCover
        (fullRefinementDatum Dsource)
        (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
        P.epsilon_pos.le hepsilonHalf))
      (sourceMassCoarseTubePartition
        (activeFineRestrictedScaleCover (canonicalBufferedTauActiveCover
          (fullRefinementDatum Dsource)
          (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf))
        (tau_le_canonicalBufferedRadius W hDsource.delta_pos
          P.epsilon_pos.le)
        (activeFineRestrictedShading
          (canonicalBufferedTauActiveCover
            (fullRefinementDatum Dsource)
            (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
            P.epsilon_pos.le hepsilonHalf)
          (tauActiveCoarseDatum (fullRefinementDatum Dsource)
            Cmulti Sseq W).shading)
        _).asConvexFactorization
      (activeFineRestrictedShading
        (canonicalBufferedTauActiveCover
          (fullRefinementDatum Dsource)
          (fullRefinementDatum_isAdmissible hDsource) Cmulti Sseq W
          P.epsilon_pos.le hepsilonHalf)
        (tauActiveCoarseDatum (fullRefinementDatum Dsource)
          Cmulti Sseq W).shading)
      fibreCF R
      (hDsource.delta_pos.trans_le (Sseq.delta_le_tau W.m))
      (canonicalBufferedRadius_pos W hDsource.delta_pos P.epsilon_pos.le)
      (canonicalBufferedRadius_le_one W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf)
      (tau_le_canonicalBufferedRadius W hDsource.delta_pos
        P.epsilon_pos.le)
      H B hepsilonRow hbetaRow0 hbetaRow2 run hUniformityExp hFreshExp
      hUniformity hFresh middleCount (by simpa using final_cardProduct_eq)
      _ lossEta hOuterFactor hExponentBudget Aouter hbeta hGammaOne
      hepsilonHalf' hrhoHalf hfine hC htauSmall hKTEvery hAKT
      hGlobalCoarseCard hRaw hSmall hTargetEpsilon

#print axioms SameAssemblyGraphFrozenActualLedgerDirectHRowDSOClosure
#print axioms
  exists_canonicalGraphFrozenIdentity_with_actualLedgerDirectHRowDSOClosure

end
end Family8CanonicalGraphFrozenActualLedgerDirectHRowDSOV2
