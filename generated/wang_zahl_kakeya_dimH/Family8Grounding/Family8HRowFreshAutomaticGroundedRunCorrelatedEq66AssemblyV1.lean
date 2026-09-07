import Family8Grounding.Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1
import Family8Grounding.Family8Prop66RowAutomaticCorrelatedEq66InputsFromHRowFreshV1
import Mathlib.Tactic

/-!
# Automatic HRow factor in the grounded finite-run Eq. 66 assembly

The existing grounded-run assembly hard-codes a
`Prop66Eq66ComposerFromHRowFresh`, whose terminal factor uses the canonical
Frostman constant and the original thickening parameter.  The automatic
Prop. 6.6 route instead proves the honest enlarged factor at `M+` and `CF+`.

This module first isolates the factor-sandwich part of the grounded run from
the ledger calculation.  It then supplies that factor using the literal same
`HRowFreshPropertyBundle` and the automatic `M+`/`CF+` theorem.  The
repeated ledger still produces `hCount` and `hAggregateLoss` internally.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowFreshAutomaticGroundedRunCorrelatedEq66AssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8FullRefinementActualDatumV1
open Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
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
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowAutomaticCorrelatedEq66InputsFromHRowFreshV1
open Family8Prop66RowAutomaticForwardThickeningConnectorV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SameObjectCorrelatedSelectedThirdCertificateV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
variable {a b : NNReal}

/-! ## Factor-parametric grounded-run core -/

/-- Ledger-grounded correlated inputs from a displayed factor sandwich.

This is the proof core of the existing HRow grounded assembly with the row
factor made explicit.  In particular, neither the final correlated input
record nor its count/aggregate fields are inputs. -/
def groundedRun_normalizedCorrelatedEq66InputsOfFactorSandwich
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {depth : Nat} {epsilon0 beta gamma : Real}
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
    (rowFactor : ENNReal)
    (hActualToFactor :
      A.frozenCoarse.averageMultiplicity ≤ rowFactor)
    (hCoefficientToFactor :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
        rowFactor)
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
    (hGammaTwo : gamma ≤ 2)
    (hCollapsed : collapsedPrefix ≤
      outerPrefix * A.frozenCoarse.averageMultiplicity)
    (hOuterFactor : outerPrefix * rowFactor ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma)
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) ≤
        3 * P.eta W.stage) :
    {T : NormalizedLongCoreCorrelatedEq66Inputs
        Dsource hDsource Cmulti Sseq P W fine G U Y Q A
          X CKT selectorLoss sourceMass sourceDensity
            massRetentionLoss densityRetentionLoss outputEta //
      T.collapsedPrefix ≤ T.firstLoss *
        sectionEightScaleCountFrostmanFactor
          delta T.middleScale T.middleCount gamma} := by
  have hPowers :=
    power_envelopes_of_groundedPaperFactorFiniteRun_uniformLocalBudget
      run hUniformityExp hFreshExp hUniformity hFresh
  have hCountAggregate :=
    count_and_aggregate_fields_of_repeatedBadParentLedger
      Dsource hDsource Cmulti Sseq P W run.productLedger
        middleCount thirdCount firstLoss thirdLoss countLoss ledgerId
        hGammaTwo hPowers.1 hPowers.2 hExponentBudget
  have hCorrelatedPower : outerPrefix *
        (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma := by
    calc
      outerPrefix *
          (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) ≤
          outerPrefix * rowFactor :=
        mul_le_mul' le_rfl hCoefficientToFactor
      _ ≤ firstLoss * sectionEightScaleCountFrostmanFactor
          delta middleScale middleCount gamma := hOuterFactor
  have hPrefixProduced : collapsedPrefix ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma := by
    calc
      collapsedPrefix ≤
          outerPrefix * A.frozenCoarse.averageMultiplicity := hCollapsed
      _ ≤ outerPrefix * rowFactor := mul_le_mul' le_rfl hActualToFactor
      _ ≤ firstLoss * sectionEightScaleCountFrostmanFactor
          delta middleScale middleCount gamma := hOuterFactor
  let T : NormalizedLongCoreCorrelatedEq66Inputs
      Dsource hDsource Cmulti Sseq P W fine G U Y Q A
        X CKT selectorLoss sourceMass sourceDensity
          massRetentionLoss densityRetentionLoss outputEta := {
    selectedThird := selectedThird
    middleScale := middleScale
    middleCount := middleCount
    thirdCount := thirdCount
    thirdCount_eq := hThirdCount
    collapsedPrefix := collapsedPrefix
    outerPrefix := outerPrefix
    firstLoss := firstLoss
    thirdLoss := thirdLoss
    countLoss := countLoss
    collapsedPrefix_le_actualThird := by
      simpa only [selectedThird.actualThirdAverage_eq] using hCollapsed
    correlatedPrefixBudget := hCorrelatedPower
    hCount := hCountAggregate.1
    hAggregateLoss := hCountAggregate.2 }
  refine ⟨T, ?_⟩
  simpa only [T] using hPrefixProduced

/-! ## Automatic HRow adapter -/

/-- The correlated card-scale coefficient lies below the same automatic
`M+`/`CF+` factor used by the outer-factor budget.  This is the reverse
direction from `HRowFreshAutomaticCoefficientBridgeObligation`; both are
kept explicit because neither follows from the other. -/
def HRowFreshAutomaticCorrelatedCoefficientToFactor
    {delta : NNReal}
    (X selectorLoss : ENNReal) (outputEta : Real)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p))
    (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (M : NNReal) (correlationLoss : ENNReal) : Prop :=
  selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
    hRowFreshAutomaticForwardProp66Factor
      Drow Crow q cell hcell selectedCells hmass hactive B M correlationLoss

/-- Automatic `M+`/`CF+` replacement for the old composer-indexed
grounded-run assembly.

The selected-third certificate, cumulative loss powers, count field,
aggregate-loss field, correlated prefix budget, and terminal prefix bound are
all constructed inside this definition. -/
def groundedRun_normalizedCorrelatedEq66InputsOfHRowFreshAutomaticForward
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {depth : Nat} {epsilon0 beta gamma : Real}
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
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p))
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
    (hThirdToRowAvg : HRowFreshActualThirdCorrelationObligation
      Drow Crow q cell hcell selectedCells hmass hactive B
        A.frozenCoarse.averageMultiplicity correlationLoss)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b)
    (hepsilon : 0 ≤ epsilonRow)
    (hbeta0 : 0 ≤ betaRow) (hbeta2 : betaRow ≤ 2)
    (hAutomaticCoefficient : HRowFreshAutomaticCoefficientBridgeObligation
      Drow Crow q cell hcell selectedCells hmass hactive B M
        correlationLoss selectorLoss CKT)
    (hCoarseCard : Fintype.card coarseIndex = U.coarseCard)
    (hCoarsePos : 0 < Fintype.card coarseIndex)
    (hCardScaleMass : X = (Fintype.card coarseIndex : ENNReal) *
      ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (2 : Nat))
    (hCoefficientCardScale :
      CKT * volume (unitBallBody : Set Space) ≤
        128 * (delta : ENNReal) ^ (-outputEta) * X)
    (hFourthCardScale :
      ((canonicalBufferedRadius W : NNReal) : ENNReal) ^ (4 : Nat) * X ≤ 1)
    (hSourceMass : sourceMass ≤
      massRetentionLoss * shadingMassOn Y U.activeFine)
    (hSourceDensity : densityRetentionLoss * sourceDensity ≤
      Y.shadingDensity)
    (hCoefficientToFactor : HRowFreshAutomaticCorrelatedCoefficientToFactor
      (delta := delta) X selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B M correlationLoss)
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
    (hGammaTwo : gamma ≤ 2)
    (hCollapsed : collapsedPrefix ≤
      outerPrefix * A.frozenCoarse.averageMultiplicity)
    (hOuterFactor : outerPrefix *
        hRowFreshAutomaticForwardProp66Factor
          Drow Crow q cell hcell selectedCells hmass hactive B M
            correlationLoss ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma)
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) ≤
        3 * P.eta W.stage) :
    {T : NormalizedLongCoreCorrelatedEq66Inputs
        Dsource hDsource Cmulti Sseq P W fine G U Y Q A
          X CKT selectorLoss sourceMass sourceDensity
            massRetentionLoss densityRetentionLoss outputEta //
      T.collapsedPrefix ≤ T.firstLoss *
        sectionEightScaleCountFrostmanFactor
          delta T.middleScale T.middleCount gamma} := by
  let selectedThird :=
    sameObjectSelectedThirdOfHRowFreshAutomaticForward
      U Y Q A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B M hthick
        correlationLoss hcorrelationTop hThirdToRowAvg hbHalf ha hab
        hepsilon hbeta0 hbeta2 hAutomaticCoefficient hCoarseCard hCoarsePos
        hCardScaleMass hCoefficientCardScale hFourthCardScale
        hSourceMass hSourceDensity
  let rowFactor :=
    hRowFreshAutomaticForwardProp66Factor
      Drow Crow q cell hcell selectedCells hmass hactive B M correlationLoss
  have hActualToFactor :
      A.frozenCoarse.averageMultiplicity ≤ rowFactor := by
    simpa only [rowFactor] using
      actualThirdAverage_le_automaticForwardProp66Factor
        Drow Crow q cell hcell selectedCells hmass hactive B M hthick
          A.frozenCoarse.averageMultiplicity correlationLoss
          hcorrelationTop hThirdToRowAvg hbHalf ha hab
          hepsilon hbeta0 hbeta2
  have hCoefficientToFactor' :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
        rowFactor := by
    simpa only [HRowFreshAutomaticCorrelatedCoefficientToFactor,
      rowFactor] using hCoefficientToFactor
  exact groundedRun_normalizedCorrelatedEq66InputsOfFactorSandwich
    Dsource hDsource Cmulti Sseq P W fine G U Y Q A
      X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
        densityRetentionLoss outputEta selectedThird rowFactor
      hActualToFactor hCoefficientToFactor' run hUniformityExp hFreshExp
      hUniformity hFresh middleScale middleCount thirdCount hThirdCount
      collapsedPrefix outerPrefix firstLoss thirdLoss countLoss ledgerId
      hGammaTwo hCollapsed hOuterFactor hExponentBudget

#print axioms groundedRun_normalizedCorrelatedEq66InputsOfFactorSandwich
#print axioms HRowFreshAutomaticCorrelatedCoefficientToFactor
#print axioms
  groundedRun_normalizedCorrelatedEq66InputsOfHRowFreshAutomaticForward

end
end Family8HRowFreshAutomaticGroundedRunCorrelatedEq66AssemblyV1
