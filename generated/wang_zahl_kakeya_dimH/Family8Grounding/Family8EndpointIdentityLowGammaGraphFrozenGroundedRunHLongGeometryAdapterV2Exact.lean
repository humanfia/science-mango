import Family8Grounding.Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
import Family8Grounding.Family8CanonicalGraphFrozenActiveParentRecoveryV1
import Family8Grounding.Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
import Family8Grounding.Family8EndpointIdentityLowGammaGroundedRunHLongGeometryAdapterV1
import Family8Grounding.Family8EndpointLongCoreSixteenthRadiusThresholdV1
import Family8Grounding.Family8NormalizedLongCoreTauActiveRestrictedGlobalCardIdentityV1
import Family8Grounding.Family8StickyParentPopularCanonicalUnionV1
import Mathlib.Tactic

/-!
# Exact low-gamma selection-first graph/frozen LongGeometry adapter, V2

The raw graph theorem selects the literal identity `R` first.  The square
plank owner setup `H` is then selected on the graph carried by that same `R`.
The analytic context below is parameterized by both selections, so it never
asks for an assembly equality or reselects an H-row.

Raw Equation (66), the actual frozen third loss, the three ledger losses, and
the correlated ledger identification are all supplied internally by the
selection-first actual-ledger closure.  The only displayed-coefficient seam
left here is its forward domination by `R.graphAverage`; the exact
`R.graphAverage -> H.loss * same-row average` direction is a theorem.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 12000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV2Exact

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8ActualThirdSelectedCoefficientFromFrozenComparableV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8BufferedCommonScaleTubePlankV1
open Family8CanonicalGraphFrozenActualLedgerSelectionFirstDSOV1
open Family8CanonicalGraphFrozenActiveParentRecoveryV1
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ContractedJohnActualTubeProxyV1
open Family8CorrelatedEq66ActualFrozenThirdLedgerBindingV1
open Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityLowGammaGroundedRunHLongGeometryAdapterV1
open Family8EndpointIdentityParameterLadderProducerV2
open Family8EndpointLongCoreSixteenthRadiusThresholdV1
open Family8FullRefinementActualDatumV1
open Family8HRowSourceAverageRetentionFromOwnerSelectionV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongCoreTauActiveRestrictedGlobalCardIdentityV1
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
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
open Family8Prop66RowAutomaticForwardThickeningConnectorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyGraphContractedJohnProxyDatumV2
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickyParentPopularCanonicalUnionV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
variable {depth : Nat} {epsilon0 beta gamma targetEpsilon : Real}

/-! ## Automatically selected literal graph row -/

/-- The fixed one-eighth buffer makes the literal square-plank side at most
one half.  This removes the old free `hbHalf` row premise. -/
theorem bufferedCommonWidth_le_half (d : NNReal) :
    bufferedCommonWidth d <= (2 : NNReal)⁻¹ := by
  calc
    bufferedCommonWidth d = (8 : NNReal)⁻¹ * maxWitnessCommonWidth d := rfl
    _ <= (8 : NNReal)⁻¹ * 1 :=
      mul_le_mul' le_rfl (maxWitnessCommonWidth_le_one d)
    _ <= (2 : NNReal)⁻¹ := by
      apply NNReal.coe_le_coe.mp
      norm_num [NNReal.coe_mul, NNReal.coe_inv]

/-- Short name for the exact square-plank datum built from the graph on `R`. -/
abbrev LiteralSelectedGraphRow
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {fine : UniformTubeFamily tau fineIndex}
    {U : StickyScaleCover fine rho}
    {Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily}
    {Y : Shading fine.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (htauRho : tau <= rho) :=
  sameAssemblyGraphBufferedPlankDatum
    R htau hrho hrhoOne htauRho
      (Family8CanonicalGraphFrozenActiveParentRecoveryV1.SameAssemblyFullCoefficientGraphIdentity.k_mem_activeCoarse R)

/-! ## Genuine downstream data after `R` and `H` have been selected -/

/-- The remaining literal inputs after the graph identity `R` and its exact
square-plank owner setup `H` have been selected.

Absent by construction: an assembly field/equality, raw Eq. (66), any free
first/third/count ledger loss, ledger identification, arbitrary row/cell
data, a free thick-control constant, a free row-correlation loss, and the
coarse-card positivity/equality proofs. -/
structure SelectedGraphFrozenActualLedgerContext
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
    (collapsedPrefix : ENNReal) (outputEta : Real)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (htau : 0 < Sseq.tau W.m)
    (hrho : 0 < canonicalBufferedRadius W)
    (hrhoOne : canonicalBufferedRadius W <= 1)
    (htauRho : Sseq.tau W.m <= canonicalBufferedRadius W)
    (H : SquarePlankHRowSelectionFirstSetup
      (LiteralSelectedGraphRow R htau hrho hrhoOne htauRho)) where
  sourceDef212Constant : NNReal
  sourceExact : ExactScaleDef212Inputs Cmulti.base sourceDef212Constant
  CKT : ENNReal
  selectorLoss : ENNReal
  sourceMass : ENNReal
  sourceDensity : ENNReal
  massRetentionLoss : ENNReal
  densityRetentionLoss : ENNReal
  hFrozenBase : FrozenComparableSelectedCoefficientBaseBudget
    Y Q R.A CKT selectorLoss
  hDisplayedToGraph :
    selectorLoss *
        (128 * (delta : ENNReal) ^ (-outputEta) *
          ((U.coarseCard : ENNReal) *
            ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (2 : Nat))) <=
      R.graphAverage
  epsilonRow : Real
  betaRow : Real
  etaRow : Real
  B : HRowFreshPropertyBundle
    (LiteralSelectedGraphRow R htau hrho hrhoOne htauRho)
    H.C H.q universalHRowCell universalHRowCell_measurable
    (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
      epsilonRow betaRow etaRow
  hepsilonRow : 0 <= epsilonRow
  hbetaRow0 : 0 <= betaRow
  hbetaRow2 : betaRow <= 2
  hCoefficientCardScale :
    CKT * volume (unitBallBody : Set Space) <=
      128 * (delta : ENNReal) ^ (-outputEta) *
        ((U.coarseCard : ENNReal) *
          ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (2 : Nat))
  hFourthCardScale :
    ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (4 : Nat) *
        ((U.coarseCard : ENNReal) *
          ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (2 : Nat)) <= 1
  hSourceMass : sourceMass <=
    massRetentionLoss * shadingMassOn Y U.activeFine
  hSourceDensity : densityRetentionLoss * sourceDensity <= Y.shadingDensity
  runN : Nat
  sourceStage : Nat
  finalStage : Nat
  finalState : PaperFactorState
  run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
    (correlatedEq66FullRefinementSingletonSourceState Dsource hDsource
      Cmulti sourceDef212Constant sourceExact) finalState
  uniformityExp : Real
  freshExp : Real
  hUniformityExp : 0 <= uniformityExp
  hFreshExp : 0 <= freshExp
  hUniformity : forall step, step ∈ run.productLedger.steps ->
    step.uniformityLoss <=
      ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
        (-uniformityExp)
  hFresh : forall step, step ∈ run.productLedger.steps ->
    step.freshRetentionLoss <=
      ((reconstructedSourceRadius run.productLedger : NNReal) : ENNReal) ^
        (-freshExp)
  middleCount : Nat
  final_cardProduct_eq : factorCardProduct finalState.factors =
    ((middleCount * U.coarseCard : Nat) : ENNReal)
  outerPrefix : ENNReal
  hCollapsed : collapsedPrefix <=
    outerPrefix * R.A.frozenCoarse.averageMultiplicity
  hOuterFactor : outerPrefix *
      hRowFreshAutomaticForwardProp66Factor
        (LiteralSelectedGraphRow R htau hrho hrhoOne htauRho)
        H.C H.q universalHRowCell universalHRowCell_measurable
        (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
          B (Fintype.card {i // i ∈ sameAssemblyGraph R} : NNReal) H.loss <=
    residualFirstLedgerLoss run.productLedger R.A *
      sectionEightScaleCountFrostmanFactor
        delta (canonicalBufferedRadius W) middleCount gamma
  hExponentBudget :
    ((runN : Real) * (uniformityExp + freshExp)) +
        ((runN : Real) * uniformityExp) * (1 - gamma / 2) <=
      3 * P.eta W.stage
  Aouter : NNReal
  hC : canonicalFrostmanConstant
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarseFamily
      closedBallFourBody <=
    (Sseq.tau W.m : ENNReal) ^
      (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
        P W.stage)
  htauSmall : Sseq.tau W.m <=
    Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
      P W.stage
  hKTEvery : Cmulti.base.IsKatzTaoAtEveryScale (Aouter : ENNReal)
  hAKT : 1024 * Aouter <=
    Sseq.tau W.m ^
      (-longIntervalDeltaLoss P.epsilon
        (10 * P.eta W.stage / (P.epsilon * beta)))

/-! ## Exact consumption of the selection-first closure -/

theorem SelectedGraphFrozenActualLedgerContext.toDividingScaleOutput
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
    (collapsedPrefix : ENNReal) (outputEta : Real)
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (htau : 0 < Sseq.tau W.m)
    (hrho : 0 < canonicalBufferedRadius W)
    (hrhoOne : canonicalBufferedRadius W <= 1)
    (htauRho : Sseq.tau W.m <= canonicalBufferedRadius W)
    (H : SquarePlankHRowSelectionFirstSetup
      (LiteralSelectedGraphRow R htau hrho hrhoOne htauRho))
    (K : SelectedGraphFrozenActualLedgerContext
      Dsource hDsource Cmulti Sseq P W fine U Q Y fibreCF R
        collapsedPrefix outputEta hepsilonHalf htau hrho hrhoOne htauRho H)
    (hClosure : SameAssemblyGraphFrozenActualLedgerDSOClosure.{0}
      (targetEpsilon := targetEpsilon)
      Dsource hDsource Cmulti Sseq P W fine U Q Y fibreCF R
        collapsedPrefix)
    (hbeta : 0 < beta) (hLowGamma : gamma <= 2 / 3)
    (hbufferedSixteenth : canonicalBufferedRadius W <= (1 / 16 : NNReal))
    (hFsource : FrostmanHypotheses Dsource outputEta)
    (hGlobalCoarseCard : U.coarseCard =
      (canonicalBufferedGlobalCover W hDsource.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card)
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput Dsource P targetEpsilon := by
  let Drow := LiteralSelectedGraphRow R htau hrho hrhoOne htauRho
  letI : Nonempty {i // i ∈ sameAssemblyGraph R} :=
    Finset.nonempty_coe_sort.mpr
      (Classical.choice R.graphCertificate).graph_nonempty
  let M : NNReal := Fintype.card {i // i ∈ sameAssemblyGraph R}
  have hGammaOne : gamma <= 1 := by linarith
  have hrhoHalf : canonicalBufferedRadius W <= (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans (by
      apply NNReal.coe_le_coe.mp
      norm_num [NNReal.coe_div, NNReal.coe_inv])
  have hfine :
      (fullRefinementDatum Dsource).family.refinement.refined.Nonempty := by
    have hmass : Dsource.shading.shadingMass ≠ 0 := by
      have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
        Dsource hDsource hFsource
      exact ne_of_gt ((ENNReal.rpow_pos
        (ENNReal.coe_pos.mpr hDsource.delta_pos)
          ENNReal.coe_ne_top).trans_le hfloor)
    let hindex : Nonempty sourceIndex :=
      nonempty_of_shadingMass_pos Dsource.shading
        (bot_lt_iff_ne_bot.mpr hmass)
    rw [fullRefinementDatum_refined]
    let i : sourceIndex := Classical.choice hindex
    exact ⟨i, Finset.mem_univ i⟩
  have ha : 0 < bufferedCommonWidth
      (contractedJohnProxyRadius (Sseq.tau W.m) (canonicalBufferedRadius W)) :=
    bufferedCommonWidth_pos
      (stickyFiberContractedJohnProxyDatum_delta_pos htau hrho)
  have hbHalf : bufferedCommonWidth
      (contractedJohnProxyRadius (Sseq.tau W.m) (canonicalBufferedRadius W)) <=
        (2 : NNReal)⁻¹ := bufferedCommonWidth_le_half _
  have hthick : FrostmanThickenedPlankControl Drow M := by
    simpa only [Drow, M] using
      squarePlank_fintypeCard_frostmanThickenedPlankControl Drow ha
  have hcorrelationTop : H.loss ≠ (⊤ : ENNReal) := by
    unfold SquarePlankHRowSelectionFirstSetup.loss ownerBucketToHRowLoss
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.natCast_ne_top _))
  have hGraphToSameRow : R.graphAverage <= H.loss *
      (HRowFreshPlankDatum
        Drow H.C H.q universalHRowCell universalHRowCell_measurable
        (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
          K.B.tau K.B.S).shading.averageMultiplicity := by
    simpa only [Drow] using
      graphAverage_le_setupLoss_mul_sameHRowAverage
        R htau hrho hrhoOne htauRho
          (Family8CanonicalGraphFrozenActiveParentRecoveryV1.SameAssemblyFullCoefficientGraphIdentity.k_mem_activeCoarse R) H K.B
  have hSelectedCoarsePos : 0 < U.coarseCard := by
    simpa using (Fintype.card_pos_iff.mpr
      (show Nonempty (Fin U.coarseCard) from ⟨R.k⟩))
  exact hClosure K.sourceDef212Constant K.sourceExact
    ((U.coarseCard : ENNReal) *
      ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (2 : Nat))
    K.CKT K.selectorLoss K.sourceMass K.sourceDensity
    K.massRetentionLoss K.densityRetentionLoss outputEta
    {i // i ∈ sameAssemblyGraph R}
    (bufferedCommonWidth
      (contractedJohnProxyRadius (Sseq.tau W.m) (canonicalBufferedRadius W)))
    (bufferedCommonWidth
      (contractedJohnProxyRadius (Sseq.tau W.m) (canonicalBufferedRadius W)))
    Drow 1 H.C H.q Unit universalHRowCell universalHRowCell_measurable
    (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
    K.epsilonRow K.betaRow K.etaRow K.B M hthick H.loss hcorrelationTop
    K.hFrozenBase K.hDisplayedToGraph hGraphToSameRow hbHalf ha le_rfl
    K.hepsilonRow K.hbetaRow0 K.hbetaRow2 hSelectedCoarsePos rfl
    K.hCoefficientCardScale K.hFourthCardScale K.hSourceMass K.hSourceDensity
    K.runN K.sourceStage K.finalStage K.finalState K.run
    K.uniformityExp K.freshExp K.hUniformityExp K.hFreshExp
    K.hUniformity K.hFresh (canonicalBufferedRadius W) K.middleCount
    K.final_cardProduct_eq K.outerPrefix K.hCollapsed K.hOuterFactor
    K.hExponentBudget K.Aouter hbeta hGammaOne hepsilonHalf hrhoHalf hfine
    K.hC K.htauSmall K.hKTEvery K.hAKT rfl hGlobalCoarseCard
    hSmall hTargetEpsilon

#print axioms bufferedCommonWidth_le_half
#print axioms SelectedGraphFrozenActualLedgerContext
#print axioms SelectedGraphFrozenActualLedgerContext.toDividingScaleOutput

end
end Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV2Exact
