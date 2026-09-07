import Family8Grounding.Family8Prop66RowActualThirdEq66PrefixBridgeV1
import Family8Grounding.Family8Prop66RowCorrelatedEq66InputsFromHRowFreshV1
import Family8Grounding.Family8PaperFactorFiniteRunPowerEnvelopeV1
import Family8Grounding.Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
import Mathlib.Tactic

/-!
# A grounded finite run and one HRow fresh composer at the Eq. 66 input seam

This is the end-to-end pre-DSO assembly.  It retains one generalized HRow
fresh composer, proves the collapsed-prefix estimate through its literal row
factor, obtains the two cumulative loss powers from a selector-grounded V2
finite run, and invokes the repeated-ledger connector to produce `hCount` and
`hAggregateLoss`.

The only scalar inputs left are pointwise powers for the actual `C_j` and
`L_j`, the ledger's same-object card/radius identification, the outer row
factor budget, the coefficient-to-row-factor bridge, and the exponent budget.
No cumulative power, count conclusion, aggregate conclusion, Equation (66)
triple, or dividing-scale output is assumed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8FullRefinementActualDatumV1
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
open Family8Prop66RowCorrelatedEq66InputsFromHRowFreshV1
open Family8RepeatedBadParentLedgerCorrelatedEq66ConnectorV1
open Family8SameObjectCorrelatedSelectedThirdCertificateV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
variable {a b : NNReal}

/-! ## The general-`tau` version of the prefix bridge -/

/-- The established prefix bridge is a three-line scalar argument.  This is
its general-`tau` form for `Prop66Eq66ComposerFromHRowFresh`; it does not
introduce a fixed-`theta` proxy row. -/
theorem collapsedPrefix_le_sectionEight_of_hRowFreshComposer
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {F : ConvexFamily fineIndex} {G : ConvexFamily coarseIndex}
    (Q : ConvexFactorization F G) (Y : Shading F)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p))
    (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow gamma : Real} {M : NNReal}
    {correlationLoss collapsedPrefix outerPrefix firstLoss : ENNReal}
    {delta middleScale : NNReal} {middleCount : Nat}
    (Z : Prop66Eq66ComposerFromHRowFresh
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow M
        A.frozenCoarse.averageMultiplicity correlationLoss)
    (hCollapsed : collapsedPrefix ≤
      outerPrefix * A.frozenCoarse.averageMultiplicity)
    (hOuterRowFactor : outerPrefix *
        hRowFreshProp66Factor
          Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma) :
    collapsedPrefix ≤ firstLoss *
      sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma := by
  calc
    collapsedPrefix ≤
        outerPrefix * A.frozenCoarse.averageMultiplicity := hCollapsed
    _ ≤ outerPrefix *
        hRowFreshProp66Factor
          Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M :=
      mul_le_mul' le_rfl Z.actualThirdAverage_le_prop66Factor
    _ ≤ firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma := hOuterRowFactor

/-! ## Earliest coefficient bridge for the correlated-input record -/

/-- The correlated certificate's displayed card-scale coefficient is
identified below the same HRow factor used by the prefix bridge. -/
def HRowFreshCorrelatedCoefficientToRowFactor
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
    (M : NNReal) : Prop :=
  selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
    hRowFreshProp66Factor
      Drow Crow q cell hcell selectedCells hmass hactive B M

/-! ## End-to-end grounded assembly -/

/-- Produce the normalized correlated Eq. 66 input record together with the
direct general-HRow prefix proof.  The record's `hCount` and
`hAggregateLoss` fields are filled by the grounded ledger theorem below. -/
def groundedRun_normalizedCorrelatedEq66InputsOfHRowFresh
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
    (hGammaTwo : gamma ≤ 2)
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
  have hForwardPower := hPowers.1
  have hReversePower := hPowers.2
  have hCountAggregate :=
    count_and_aggregate_fields_of_repeatedBadParentLedger
      Dsource hDsource Cmulti Sseq P W run.productLedger
        middleCount thirdCount firstLoss thirdLoss countLoss ledgerId
        hGammaTwo hForwardPower hReversePower hExponentBudget
  have hCountProduced := hCountAggregate.1
  have hAggregateProduced := hCountAggregate.2
  have hCorrelatedPower : outerPrefix *
        (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma := by
    calc
      outerPrefix *
          (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) ≤
          outerPrefix * hRowFreshProp66Factor
            Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M :=
        mul_le_mul' le_rfl hCoefficientToRow
      _ ≤ firstLoss * sectionEightScaleCountFrostmanFactor
          delta middleScale middleCount gamma := hOuterRowFactor
  have hPrefixProduced := collapsedPrefix_le_sectionEight_of_hRowFreshComposer
    Q Y A Drow Crow q cell hcell selectedCells hmass hactive Z
      hCollapsed hOuterRowFactor
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
    hCount := hCountProduced
    hAggregateLoss := hAggregateProduced }
  refine ⟨T, ?_⟩
  simpa only [T] using hPrefixProduced

#print axioms collapsedPrefix_le_sectionEight_of_hRowFreshComposer
#print axioms HRowFreshCorrelatedCoefficientToRowFactor
#print axioms groundedRun_normalizedCorrelatedEq66InputsOfHRowFresh

end
end Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1
