import Family8Grounding.Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV2ActualSelected
import Family8Grounding.Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOLocalCapV1
import Mathlib.Tactic

/-!
# Strict selected-actual low-gamma adapter from a local first-outer cap, V3

V2 asked for `KatzTaoHypotheses Dsource etaKT`.  The Eq. (66) chain used only
one consequence of its concentration half: a fibre-cardinality cap on the
single source-to-`tau_m` cover selected by `W`.  V3 exposes precisely that
same-object local cap.  It does not quantify over alternative witnesses,
graphs, or H-row setups.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 14000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV3SelectedLocalCap

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalGraphFrozenActiveParentRecoveryV1
open Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
open Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOLocalCapV1
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV2Exact
open Family8EndpointIdentityLowGammaGroundedRunHLongGeometryAdapterV1
open Family8EndpointIdentityParameterLadderProducerV2
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalRawEq66GraphFrozenLocalCapV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongCoreTauActiveBasicTransportsV2
open Family8NormalizedLongCoreTauActiveRestrictedGlobalCardIdentityV1
open Family8NormalizedLongIntervalCanonicalBufferedCoverV1.Witness
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyParentPopularCanonicalUnionV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {epsilon0 beta gamma : Real}

/-! ## Context only at the selected witness, graph, and row -/

abbrev SelectedActualGraphFrozenLedgerLocalCapDatumContext
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (Dsource : ActualTubeDatum delta sourceIndex)
    (hDsource : Dsource.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    {depth : Nat}
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (Sseq : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum Dsource).family Cmulti
        P.N P.epsilon P.eta Sseq)
    (targetEpsilon etaKT sourceEta : Real)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    (hFSource : FrostmanHypotheses Dsource sourceEta)
    (hSourceEta : 0 < sourceEta)
    (hdeltaFrozen : delta <=
      activeFrozenComparableLossAbsorptionThreshold sourceEta) : Prop :=
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
        Dsource hDsource hFSource
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
  let htau : 0 < Sseq.tau W.m :=
    hDsource.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  let hrho : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hDsource.delta_pos P.epsilon_pos.le
  let hrhoOne : canonicalBufferedRadius W <= 1 :=
    canonicalBufferedRadius_le_one W hDsource.delta_pos
      P.epsilon_pos.le hepsilonHalf
  let htauRho : Sseq.tau W.m <= canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hDsource.delta_pos P.epsilon_pos.le
  exists fibreCF : ENNReal,
  exists hCFfinite : fibreCF ≠ ∞,
  exists hFibres : T.IsFrostmanAtScale fibreCF,
  exists hFirstCap : SelectedSourceTauFibreCap
      Dsource Cmulti Sseq W etaKT,
    let hSelection :=
      exists_canonicalGraphFrozenIdentity_with_actualLedgerDSOClosure_of_selectedSourceTauFibreCap.{0}
        (targetEpsilon := targetEpsilon)
        Dsource hDsource Cmulti Sseq P W hepsilonHalf
          hbufferedSixteenth fibreCF hCFfinite hFibres
            hFSource hFirstCap hSourceEta hdeltaFrozen
    let R := Classical.choose hSelection
    let hk : R.k ∈ T.activeCoarse :=
      SameAssemblyFullCoefficientGraphIdentity.k_mem_activeCoarse R
    let H : SquarePlankHRowSelectionFirstSetup
        (LiteralSelectedGraphRow R htau hrho hrhoOne htauRho) :=
      Classical.choice (exists_sameAssemblyGraphHRowSelectionFirstSetup
        R htau hrho hrhoOne htauRho hk)
    Nonempty (SelectedGraphFrozenActualLedgerContext
      Dsource hDsource Cmulti Sseq P W
      (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
      fibreCF R (R.collapsedPrefix (delta := delta) firstCap sourceEta)
      sourceEta hepsilonHalf htau hrho hrhoOne htauRho H)

/-! ## Weak full-context producer with no global source KT seam -/

abbrev LowGammaSelectedActualGraphFrozenLedgerLocalCapFullContextProducer
    (P : ParameterLadder epsilon0 beta gamma) : Prop :=
  forall targetEpsilon : Real, forall _hTarget : 0 < targetEpsilon,
  forall etaKT sourceEta : Real, forall delta0 : NNReal,
  forall _hEtaKT : 0 < etaKT,
  forall _hEtaKTCap : etaKT <= P.epsilon ^ 2 * P.eta 0 / 32,
  forall hSourceEta : 0 < sourceEta,
  forall _hSourceEtaCap : sourceEta <= P.eta 0,
  forall _hDelta0 : 0 < delta0,
  forall _hDelta0Half : delta0 <= (2 : NNReal)⁻¹,
  forall _hKTExact : KatzTaoAtParameters beta
    (sectionEightFixedNu P) etaKT delta0,
  forall _hKTRelative : KatzTaoAtRelativeScaleParameters beta
    (sectionEightFixedNu P) etaKT delta0,
  forall _hFExact : FrostmanAtParameters gamma
    (sectionEightSourceLoss P targetEpsilon) sourceEta delta0,
  forall _hFRelative : FrostmanAtRelativeScaleParameters gamma
    (sectionEightSourceLoss P targetEpsilon) sourceEta delta0,
    exists contextDelta0 : NNReal, 0 < contextDelta0 /\
      forall (delta : NNReal) (sourceIndex : Type)
        [Fintype sourceIndex] [DecidableEq sourceIndex]
        (Dsource : ActualTubeDatum delta sourceIndex)
        (hDsource : Dsource.IsAdmissible),
      forall _hdelta : delta <= contextDelta0,
      forall hFSource : FrostmanHypotheses Dsource sourceEta,
      forall hepsilonHalf : P.epsilon <= 1 / 2,
      forall hdeltaFrozen : delta <=
        activeFrozenComparableLossAbsorptionThreshold sourceEta,
        exists depth : Nat,
        exists Cmulti : CoherentStickyMultiscaleCover
          (fullRefinementDatum Dsource).family,
        exists Sseq : FiniteScaleSequence delta depth,
        exists W : NormalizedLongIntervalCoreWitness
          (fullRefinementDatum Dsource).family Cmulti
            P.N P.epsilon P.eta Sseq,
        exists hbufferedSixteenth :
          canonicalBufferedRadius W <= (1 / 16 : NNReal),
          SelectedActualGraphFrozenLedgerLocalCapDatumContext
            Dsource hDsource P Cmulti Sseq W
              (4 * sectionEightSourceLoss P targetEpsilon)
              etaKT sourceEta hepsilonHalf hbufferedSixteenth
                hFSource hSourceEta hdeltaFrozen

def lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon sourceEta : Real) : NNReal :=
  min (lowGammaGroundedRunRawDelta0 P targetEpsilon)
    (activeFrozenComparableLossAbsorptionThreshold sourceEta)

theorem lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon sourceEta : Real) :
    0 < lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0
      P targetEpsilon sourceEta := by
  exact lt_min (lowGammaGroundedRunRawDelta0_pos P targetEpsilon)
    (activeFrozenComparableLossAbsorptionThreshold_pos sourceEta)

/-! ## Final strict selected-local-cap top adapter -/

theorem cappedStrongFrostman_hLongGeometry_of_selectedActualGraphFrozenLedgerLocalCapContext
    (hbeta : 0 < beta) (hgap : beta < gamma)
    (hLowGamma : gamma <= 2 / 3)
    (hContext : LowGammaSelectedActualGraphFrozenLedgerLocalCapFullContextProducer
      (endpointIdentityParameterLadder hbeta hgap)) :
    CappedStrongFrostmanHLongGeometry beta gamma := by
  let P := endpointIdentityParameterLadder hbeta hgap
  refine ⟨endpointIdentityEpsilon0 beta gamma, P, ?_⟩
  intro targetEpsilon hTarget etaKT sourceEta delta0
    hEtaKT hEtaKTCap hSourceEta hSourceEtaCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative
  have hepsilonHalf : P.epsilon <= 1 / 2 := by
    have hepsilonGap := P.epsilon_gap
    nlinarith [hLowGamma, hbeta]
  obtain ⟨contextDelta0, hContextDelta0, hContextAt⟩ :=
    hContext targetEpsilon hTarget etaKT sourceEta delta0
      hEtaKT hEtaKTCap hSourceEta hSourceEtaCap hDelta0 hDelta0Half
      hKTExact hKTRelative hFExact hFRelative
  let rawDelta0 := min contextDelta0
    (lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0
      P targetEpsilon sourceEta)
  have hRawDelta0 : 0 < rawDelta0 := by
    dsimp only [rawDelta0]
    exact lt_min hContextDelta0
      (lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0_pos
        P targetEpsilon sourceEta)
  refine ⟨rawDelta0, hRawDelta0, ?_⟩
  intro delta sourceIndex _ _ Dsource hDsource hdelta hFSource
    _hmass _callbackW
  have hdeltaContext : delta <= contextDelta0 := by
    exact hdelta.trans (by
      dsimp only [rawDelta0]
      exact min_le_left _ _)
  have hdeltaInternal : delta <=
      lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0
        P targetEpsilon sourceEta := by
    exact hdelta.trans (by
      dsimp only [rawDelta0]
      exact min_le_right _ _)
  have hdeltaDSO : delta <=
      lowGammaGroundedRunRawDelta0 P targetEpsilon := by
    exact hdeltaInternal.trans (by
      unfold lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0
      exact min_le_left _ _)
  have hdeltaFrozen : delta <=
      activeFrozenComparableLossAbsorptionThreshold sourceEta := by
    exact hdeltaInternal.trans (by
      unfold lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0
      exact min_le_right _ _)
  obtain ⟨depth, Cmulti, Sseq, W, hbufferedSixteenth, hPayload⟩ :=
    hContextAt delta sourceIndex Dsource hDsource hdeltaContext
      hFSource hepsilonHalf hdeltaFrozen
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
        Dsource hDsource hFSource
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
  let htau : 0 < Sseq.tau W.m :=
    hDsource.delta_pos.trans_le (Sseq.delta_le_tau W.m)
  let hrho : 0 < canonicalBufferedRadius W :=
    canonicalBufferedRadius_pos W hDsource.delta_pos P.epsilon_pos.le
  let hrhoOne : canonicalBufferedRadius W <= 1 :=
    canonicalBufferedRadius_le_one W hDsource.delta_pos
      P.epsilon_pos.le hepsilonHalf
  let htauRho : Sseq.tau W.m <= canonicalBufferedRadius W :=
    tau_le_canonicalBufferedRadius W hDsource.delta_pos P.epsilon_pos.le
  obtain ⟨fibreCF, hCFfinite, hFibres, hFirstCap, hSelectedContext⟩ :=
    hPayload
  let hSelection :=
    exists_canonicalGraphFrozenIdentity_with_actualLedgerDSOClosure_of_selectedSourceTauFibreCap.{0}
      (targetEpsilon := 4 * sectionEightSourceLoss P targetEpsilon)
      Dsource hDsource Cmulti Sseq P W hepsilonHalf
        hbufferedSixteenth fibreCF hCFfinite hFibres
          hFSource hFirstCap hSourceEta hdeltaFrozen
  let R := Classical.choose hSelection
  have hClosure : SameAssemblyGraphFrozenActualLedgerDSOClosure
      (targetEpsilon := 4 * sectionEightSourceLoss P targetEpsilon)
      Dsource hDsource Cmulti Sseq P W
      (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
      fibreCF R (R.collapsedPrefix (delta := delta) firstCap sourceEta) := by
    exact (Classical.choose_spec hSelection).2
  let hk : R.k ∈ T.activeCoarse :=
    SameAssemblyFullCoefficientGraphIdentity.k_mem_activeCoarse R
  let H : SquarePlankHRowSelectionFirstSetup
      (LiteralSelectedGraphRow R htau hrho hrhoOne htauRho) :=
    Classical.choice (exists_sameAssemblyGraphHRowSelectionFirstSetup
      R htau hrho hrhoOne htauRho hk)
  obtain ⟨K⟩ := hSelectedContext
  have hGlobalCoarseCard : T.coarseCard =
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card := by
    calc
      T.coarseCard = U0.activeCoarse.card := rfl
      _ = (activeFineRestrictedScaleCover U0).activeCoarse.card := by
        simp only [activeFineRestrictedScaleCover_activeCoarse,
          Finset.card_univ, Fintype.card_fin]
        rfl
      _ = (canonicalBufferedGlobalCover W hDsource.delta_pos
          P.epsilon_pos.le hepsilonHalf).activeCoarse.card := by
        simpa only [U0] using
          canonicalBufferedTauActiveRestricted_activeCoarse_card_eq_global
            E hE Cmulti Sseq W P.epsilon_pos.le hepsilonHalf
  have hSmall : delta <= sectionEightThreeScaleActualThreshold gamma
      ((4 * sectionEightSourceLoss P targetEpsilon) / 4) := by
    simpa only [lowGammaGroundedRunRawDelta0,
      show (4 * sectionEightSourceLoss P targetEpsilon) / 4 =
        sectionEightSourceLoss P targetEpsilon by ring] using hdeltaDSO
  have hEffectiveTarget :
      0 < 4 * sectionEightSourceLoss P targetEpsilon := by
    have hSourceLoss : 0 < sectionEightSourceLoss P targetEpsilon :=
      sectionEightSourceLoss_pos P hTarget
    positivity
  exact K.toDividingScaleOutput
    (targetEpsilon := 4 * sectionEightSourceLoss P targetEpsilon)
    Dsource hDsource Cmulti Sseq P W
      (activeFineRestrictedFamily U0) T Psource.asConvexFactorization YR
      fibreCF R (R.collapsedPrefix (delta := delta) firstCap sourceEta)
      sourceEta hepsilonHalf htau hrho hrhoOne htauRho H hClosure
      hbeta hLowGamma hbufferedSixteenth hFSource hGlobalCoarseCard
      hSmall hEffectiveTarget

#print axioms SelectedActualGraphFrozenLedgerLocalCapDatumContext
#print axioms
  LowGammaSelectedActualGraphFrozenLedgerLocalCapFullContextProducer
#print axioms
  lowGammaSelectedActualGraphFrozenLedgerLocalCapRawDelta0_pos
#print axioms
  cappedStrongFrostman_hLongGeometry_of_selectedActualGraphFrozenLedgerLocalCapContext

end
end Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV3SelectedLocalCap
