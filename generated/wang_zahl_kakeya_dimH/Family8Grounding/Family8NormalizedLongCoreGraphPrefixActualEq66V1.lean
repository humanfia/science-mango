import Family8Grounding.Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
import Family8Grounding.Family8HRowFreshAutomaticGroundedRunCorrelatedEq66AssemblyV1
import Family8Grounding.Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
import Family8Grounding.Family8NormalizedLongCoreEq66FactorOneV2
import Mathlib.Tactic

/-!
# Graph-prefix route to the actual Eq. 66 terminal interface

The selected graph average belongs to the first/collapsed prefix, not to the
frozen third factor.  This module keeps that factorization literal.  It sends

`collapsedPrefix <= outerPrefix * graphAverage`

through the already selected H-row factor and stores only the actual prefix
budget consumed by the terminal DSO connector.  No displayed coefficient and
no comparison from the frozen third average to the H-row is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 7000000

open scoped ENNReal NNReal

namespace Family8NormalizedLongCoreGraphPrefixActualEq66V1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8BufferedCommonScaleTubePlankV1
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ContractedJohnActualTubeProxyV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8HRowSourceAverageRetentionFromOwnerSelectionV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1
open Family8NormalizedLongCoreActualPrefixEq66ToDSOV1.NormalizedLongCoreActualPrefixEq66Inputs
open Family8NormalizedLongCoreEq66FactorOneV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunPowerEnvelopeV1
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorFiniteRunV2.GroundedPaperFactorFiniteRun
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowAutomaticForwardThickeningConnectorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat} {epsilon0 beta gamma : Real}

/-! ## Literal graph factorization -/

/-- The canonical graph-frozen collapsed prefix is definitionally an outer
coefficient times the selected graph average. -/
theorem sameAssembly_collapsedPrefix_eq_graphProduct
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {fine : UniformTubeFamily tau fineIndex}
    {U : StickyScaleCover fine rho}
    {Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily}
    {Y : Shading fine.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    (firstCap : ENNReal) (lossEta : Real) :
    R.collapsedPrefix (delta := delta) firstCap lossEta =
      ((firstCap * (4 * (delta : ENNReal) ^ (-lossEta))) * R.graphLoss) *
        R.graphAverage := rfl

/-- Hence the only scalar comparison required to place the literal graph
prefix below an externally named `outerPrefix` is a comparison of their
outer coefficients. -/
theorem sameAssembly_collapsedPrefix_le_outer_mul_graphAverage
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {fine : UniformTubeFamily tau fineIndex}
    {U : StickyScaleCover fine rho}
    {Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily}
    {Y : Shading fine.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    (firstCap : ENNReal) (lossEta : Real) (outerPrefix : ENNReal)
    (hOuter :
      (firstCap * (4 * (delta : ENNReal) ^ (-lossEta))) * R.graphLoss ≤
        outerPrefix) :
    R.collapsedPrefix (delta := delta) firstCap lossEta ≤
      outerPrefix * R.graphAverage := by
  rw [sameAssembly_collapsedPrefix_eq_graphProduct]
  exact mul_le_mul' hOuter le_rfl

/-! ## Direct selected-graph H-row factor -/

theorem graphBufferedCommonWidth_le_half (d : NNReal) :
    bufferedCommonWidth d ≤ (2 : NNReal)⁻¹ := by
  calc
    bufferedCommonWidth d = (8 : NNReal)⁻¹ * maxWitnessCommonWidth d := rfl
    _ ≤ (8 : NNReal)⁻¹ * 1 :=
      mul_le_mul' le_rfl (maxWitnessCommonWidth_le_one d)
    _ ≤ (2 : NNReal)⁻¹ := by
      apply NNReal.coe_le_coe.mp
      norm_num [NNReal.coe_mul, NNReal.coe_inv]

/-- The graph row selected from the same identity pays its own graph average.
This is the exact first-factor comparison used by the graph-prefix assembler;
it neither mentions the frozen third average nor a displayed coefficient. -/
theorem sameAssembly_graphAverage_le_automaticForwardProp66Factor
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    {fine : UniformTubeFamily tau fineIndex}
    {U : StickyScaleCover fine rho}
    {Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily}
    {Y : Shading fine.bodyFamily} {fibreCF : ENNReal}
    (R : SameAssemblyFullCoefficientGraphIdentity fine U Q Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ U.activeCoarse)
    (H : SquarePlankHRowSelectionFirstSetup
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk))
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        epsilon beta eta)
    (hepsilon : 0 ≤ epsilon) (hbeta0 : 0 ≤ beta) (hbeta2 : beta ≤ 2) :
    R.graphAverage ≤
      hRowFreshAutomaticForwardProp66Factor
        (sameAssemblyGraphBufferedPlankDatum
          R htau hrho hrhoOne htauRho hk)
        H.C H.q universalHRowCell universalHRowCell_measurable
        (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        B (Fintype.card {i // i ∈ sameAssemblyGraph R} : NNReal) H.loss := by
  let Drow := sameAssemblyGraphBufferedPlankDatum
    R htau hrho hrhoOne htauRho hk
  letI : Nonempty {i // i ∈ sameAssemblyGraph R} :=
    Finset.nonempty_coe_sort.mpr
      (Classical.choice R.graphCertificate).graph_nonempty
  have ha : 0 < bufferedCommonWidth
      (contractedJohnProxyRadius tau rho) :=
    bufferedCommonWidth_pos
      (stickyFiberContractedJohnProxyDatum_delta_pos htau hrho)
  have hthick : FrostmanThickenedPlankControl Drow
      (Fintype.card {i // i ∈ sameAssemblyGraph R} : NNReal) := by
    simpa only [Drow] using
      squarePlank_fintypeCard_frostmanThickenedPlankControl Drow ha
  have hcorrelationTop : H.loss ≠ (⊤ : ENNReal) := by
    unfold SquarePlankHRowSelectionFirstSetup.loss ownerBucketToHRowLoss
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
  have hGraphToSameRow : HRowFreshActualThirdCorrelationObligation
      Drow H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty B
      R.graphAverage H.loss := by
    simpa only [HRowFreshActualThirdCorrelationObligation, Drow] using
      graphAverage_le_setupLoss_mul_sameHRowAverage
        R htau hrho hrhoOne htauRho hk H B
  simpa only [Drow] using
    actualThirdAverage_le_automaticForwardProp66Factor
      Drow H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty B
      (Fintype.card {i // i ∈ sameAssemblyGraph R} : NNReal) hthick
      R.graphAverage H.loss hcorrelationTop hGraphToSameRow
      (graphBufferedCommonWidth_le_half _) ha le_rfl
      hepsilon hbeta0 hbeta2

/-! ## Grounded ledger assembler -/

/-- Build the genuinely terminal scalar package by routing the selected
graph average through the row factor.  The frozen third average is absent
from this prefix proof. -/
def groundedRun_normalizedActualPrefixEq66InputsOfGraphFactorSandwich
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (graphAverage rowFactor : ENNReal)
    (hGraphToFactor : graphAverage ≤ rowFactor)
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
    (collapsedPrefix outerPrefix firstLoss thirdLoss countLoss : ENNReal)
    (ledgerId : CorrelatedEq66LedgerIdentification
      run.productLedger delta index middleCount thirdCount
        firstLoss thirdLoss countLoss)
    (hGammaTwo : gamma ≤ 2)
    (hCollapsedGraph :
      collapsedPrefix ≤ outerPrefix * graphAverage)
    (hOuterFactor : outerPrefix * rowFactor ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma)
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) ≤
        3 * P.eta W.stage) :
    NormalizedLongCoreActualPrefixEq66Inputs D hD C S P W := by
  have hPowers :=
    power_envelopes_of_groundedPaperFactorFiniteRun_uniformLocalBudget
      run hUniformityExp hFreshExp hUniformity hFresh
  have hCountAggregate :=
    count_and_aggregate_fields_of_repeatedBadParentLedger
      D hD C S P W run.productLedger middleCount thirdCount
        firstLoss thirdLoss countLoss ledgerId hGammaTwo
        hPowers.1 hPowers.2 hExponentBudget
  exact {
    middleScale := middleScale
    middleCount := middleCount
    thirdCount := thirdCount
    collapsedPrefix := collapsedPrefix
    firstLoss := firstLoss
    thirdLoss := thirdLoss
    countLoss := countLoss
    actualPrefixBudget := by
      calc
        collapsedPrefix ≤ outerPrefix * graphAverage := hCollapsedGraph
        _ ≤ outerPrefix * rowFactor :=
          mul_le_mul' le_rfl hGraphToFactor
        _ ≤ firstLoss * sectionEightScaleCountFrostmanFactor
            delta middleScale middleCount gamma := hOuterFactor
    hCount := hCountAggregate.1
    hAggregateLoss := hCountAggregate.2 }

/-! ## Raw Equation (66) triple with an explicit coarse-count identity -/

/-- Inflate the frozen third only in the Equation-(66) triple.  The prefix
package is the minimal actual-prefix record above; the selected coarse-count
identity is supplied explicitly instead of through a selected-third proxy
certificate. -/
theorem hTriple_of_graphPrefix_rawEq66
    {fineIndex : Type} [Fintype fineIndex] [DecidableEq fineIndex]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C P.N P.epsilon P.eta S)
    (fine : UniformTubeFamily (S.tau W.m) fineIndex)
    (U : StickyScaleCover fine (canonicalBufferedRadius W))
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily U.coarse.bodyFamily)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
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
    (hThirdCount : Z.thirdCount = U.coarseCard)
    (hCoarseCard : U.coarseCard =
      (canonicalBufferedGlobalCover W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card)
    (hThirdLoss : A.frozenCoarse.averageMultiplicity ≤ Z.thirdLoss)
    (hRawEq66 : D.shading.averageMultiplicity ≤
      Z.collapsedPrefix * A.frozenCoarse.averageMultiplicity) :
    D.shading.averageMultiplicity ≤
      Z.collapsedPrefix *
        (((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss) := by
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  have hThirdCountCanonical : Z.thirdCount =
      (canonicalBufferedGlobalCover W hD.delta_pos
        P.epsilon_pos.le hepsilonHalf).activeCoarse.card :=
    hThirdCount.trans hCoarseCard
  have hFactorOneCanonical : (1 : ENNReal) ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          (canonicalBufferedRadius W) 1
          (canonicalBufferedGlobalCover W hD.delta_pos
            P.epsilon_pos.le hepsilonHalf).activeCoarse.card gamma :=
    one_le_canonicalBufferedGlobal_eq66Factor
      E hE C S P W Aouter hbeta hgamma hepsilonHalf hrhoHalf
        hfine hC htauSmall hKTEvery hAKT
  have hFactorOne : (1 : ENNReal) ≤
      (delta : ENNReal) ^ (10 * P.eta W.stage) *
        sectionEightScaleCountFrostmanFactor
          Z.middleScale 1 Z.thirdCount gamma := by
    rw [hMiddleScale, hThirdCountCanonical]
    exact hFactorOneCanonical
  have hInflatedThird : A.frozenCoarse.averageMultiplicity ≤
      ((delta : ENNReal) ^ (10 * P.eta W.stage) *
          sectionEightScaleCountFrostmanFactor
            Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss := by
    calc
      A.frozenCoarse.averageMultiplicity ≤ Z.thirdLoss := hThirdLoss
      _ = 1 * Z.thirdLoss := by rw [one_mul]
      _ ≤ ((delta : ENNReal) ^ (10 * P.eta W.stage) *
            sectionEightScaleCountFrostmanFactor
              Z.middleScale 1 Z.thirdCount gamma) * Z.thirdLoss :=
        mul_le_mul' hFactorOne le_rfl
  exact hRawEq66.trans (mul_le_mul' le_rfl hInflatedThird)

#print axioms sameAssembly_collapsedPrefix_eq_graphProduct
#print axioms sameAssembly_collapsedPrefix_le_outer_mul_graphAverage
#print axioms graphBufferedCommonWidth_le_half
#print axioms sameAssembly_graphAverage_le_automaticForwardProp66Factor
#print axioms groundedRun_normalizedActualPrefixEq66InputsOfGraphFactorSandwich
#print axioms hTriple_of_graphPrefix_rawEq66

end
end Family8NormalizedLongCoreGraphPrefixActualEq66V1
