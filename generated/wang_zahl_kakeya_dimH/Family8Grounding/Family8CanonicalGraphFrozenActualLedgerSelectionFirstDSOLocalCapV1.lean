import Family8Grounding.Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
import Family8Grounding.Family8CanonicalGraphFrozenRawEq66IdentityLocalCapBridgeV1
import Mathlib.Tactic

/-!
# Selection-first actual-ledger DSO closure from the selected local cap

This successor keeps the selected `R`, raw Equation-(66) product, and entire
actual-ledger consumer literal.  Its only change is at the earliest packing
input: the fixed source-to-`tau_m` fibre cap replaces a global source
`KatzTaoHypotheses` conjunction.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOLocalCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8ActualThirdSelectedCoefficientFromFrozenComparableV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8CanonicalGraphFrozenRawEq66IdentityLocalCapBridgeV1
open Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8FullRefinementActualDatumV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8HRowFreshAutomaticRawCorrelationsFullRefinementActualFrozenLedgerEq66ToDSOV1
open Family8HRowDisplayedCoefficientIncidenceFromMassFloorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenLocalCapV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveMiddlePowerInputsV1
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickySourceMassFactorizationRoundTripV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-- Select the canonical graph/frozen identity first and close the same
actual-ledger implication, using only the local cap at the selected `W.m`. -/
theorem exists_canonicalGraphFrozenIdentity_with_actualLedgerDSOClosure_of_selectedSourceTauFibreCap
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
    (hFirstCap : SelectedSourceTauFibreCap Dsource Cmulti Sseq W etaKT)
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
        have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
          Dsource hDsource hFsource
        exact ne_of_gt ((ENNReal.rpow_pos
          (ENNReal.coe_pos.mpr hDsource.delta_pos)
            ENNReal.coe_ne_top).trans_le hfloor)
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
    ∃ R : SameAssemblyFullCoefficientGraphIdentity
        (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
          fibreCF,
      R.A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
          (Fin U0.activeCoarse.card) ∧
      SameAssemblyGraphFrozenActualLedgerDSOClosure
        (targetEpsilon := targetEpsilon)
        Dsource hDsource Cmulti Sseq P W
        (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
        fibreCF R (R.collapsedPrefix (delta := delta) firstCap lossEta) := by
  dsimp only
  obtain ⟨R, hLoss, hRaw⟩ :=
    exists_canonicalGraphFrozenIdentity_rawEq66_of_selectedSourceTauFibreCap
      Dsource hDsource Cmulti Sseq P W hepsilonHalf hbufferedSixteenth
        fibreCF hCFfinite hFibres hFsource hFirstCap hlossEta hdeltaLoss
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

#print axioms
  exists_canonicalGraphFrozenIdentity_with_actualLedgerDSOClosure_of_selectedSourceTauFibreCap

end
end Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOLocalCapV1
