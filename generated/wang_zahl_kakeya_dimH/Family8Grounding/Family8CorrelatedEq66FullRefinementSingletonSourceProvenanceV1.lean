import Family8Grounding.Family8CorrelatedEq66LiteralSingletonSourceProvenanceV1
import Mathlib.Tactic

/-!
# Full-refinement singleton source provenance for correlated Equation (66)

The canonical source atom is the literal `fullRefinementDatum Dsource`.
Unlike the raw-source atom, its recursive hierarchy is exactly the existing
`Cmulti` used by the normalized long-core assembly.  Full refinement keeps
the radius and index type definitionally unchanged, so the singleton source
cardinality and radius products are still the original index card and
`delta`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8CorrelatedEq66LiteralSingletonSourceProvenanceV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8FullRefinementActualDatumV1
open Family8HRowFreshGroundedRunCorrelatedEq66AssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8PaperFactorFiniteRunV2
open Family8PaperFactorStateV1
open Family8ParameterLadderV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
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
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
variable {a b : NNReal}

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The actual full-refinement source atom. -/
def correlatedEq66FullRefinementSourceFactor
    (Dsource : ActualTubeDatum delta index) : ActualFactorDatum :=
  ActualFactorDatum.ofDatum (fullRefinementDatum Dsource)

/-- The canonical singleton full-refinement source list. -/
def correlatedEq66FullRefinementSourceFactors
    (Dsource : ActualTubeDatum delta index) : List ActualFactorDatum :=
  [correlatedEq66FullRefinementSourceFactor Dsource]

@[simp]
theorem correlatedEq66FullRefinementSourceFactors_cardProduct
    (Dsource : ActualTubeDatum delta index) :
    factorCardProduct
        (correlatedEq66FullRefinementSourceFactors Dsource) =
      (Fintype.card index : ENNReal) := by
  simp only [correlatedEq66FullRefinementSourceFactors,
    correlatedEq66FullRefinementSourceFactor, factorCardProduct_cons,
    ActualFactorDatum.ofDatum_card, factorCardProduct_nil, mul_one]

@[simp]
theorem correlatedEq66FullRefinementSourceFactors_radiusProduct
    (Dsource : ActualTubeDatum delta index) :
    factorRadiusProduct
        (correlatedEq66FullRefinementSourceFactors Dsource) = delta := by
  simp only [correlatedEq66FullRefinementSourceFactors,
    correlatedEq66FullRefinementSourceFactor, factorRadiusProduct_cons,
    ActualFactorDatum.ofDatum_radius, factorRadiusProduct_nil, mul_one]

/-- The H-row assembly's existing `Cmulti` supplies the literal source
coherent cover.  The only hierarchy input left is Exact Definition 2.12 for
that same cover. -/
def correlatedEq66FullRefinementSourceReadiness
    (Dsource : ActualTubeDatum delta index)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (def212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base def212Constant) :
    PaperFactorAtomReadiness
      (correlatedEq66FullRefinementSourceFactor Dsource) where
  admissible := by
    change (fullRefinementDatum Dsource).IsAdmissible
    exact fullRefinementDatum_isAdmissible hDsource
  coherentCover := Cmulti
  def212Constant := def212Constant
  exactDef212 := sourceExact

/-- The canonical full-refinement singleton source paper state. -/
def correlatedEq66FullRefinementSingletonSourceState
    (Dsource : ActualTubeDatum delta index)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (def212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base def212Constant) : PaperFactorState :=
  PaperFactorState.ofFactors
    (correlatedEq66FullRefinementSourceFactors Dsource)
    (.cons (correlatedEq66FullRefinementSourceReadiness
      Dsource hDsource Cmulti def212Constant sourceExact) .nil)

@[simp]
theorem correlatedEq66FullRefinementSingletonSourceState_factors
    (Dsource : ActualTubeDatum delta index)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (def212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base def212Constant) :
    (correlatedEq66FullRefinementSingletonSourceState
      Dsource hDsource Cmulti def212Constant sourceExact).factors =
        correlatedEq66FullRefinementSourceFactors Dsource :=
  rfl

/-- The literal full-refinement source makes all three source-side ledger
identifications automatic. -/
theorem correlatedEq66LedgerIdentification_of_fullRefinementSingletonSource
    (Dsource : ActualTubeDatum delta index)
    {finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger
      (correlatedEq66FullRefinementSourceFactors Dsource) finalFactors)
    (middleCount thirdCount : Nat) (firstLoss thirdLoss : ENNReal)
    (final_cardProduct_eq :
      factorCardProduct finalFactors =
        ((middleCount * thirdCount : Nat) : ENNReal))
    (outerLoss_le_reverse :
      firstLoss * thirdLoss <= cumulativeReverseLoss ledger) :
    CorrelatedEq66LedgerIdentification ledger delta index
      middleCount thirdCount firstLoss thirdLoss
        (cumulativeForwardLoss ledger) where
  source_cardProduct_eq :=
    correlatedEq66FullRefinementSourceFactors_cardProduct Dsource
  final_cardProduct_eq := final_cardProduct_eq
  source_radiusProduct_eq_delta :=
    correlatedEq66FullRefinementSourceFactors_radiusProduct Dsource
  countLoss_eq_forward := rfl
  outerLoss_le_reverse := outerLoss_le_reverse

/-- Direct producer for the exact ledger-identification argument of the H-row
consumer when its grounded run starts at the canonical full-refinement state. -/
theorem groundedRun_correlatedEq66LedgerIdentification_of_fullRefinementState
    (Dsource : ActualTubeDatum delta index)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (def212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base def212Constant)
    {runN sourceStage finalStage : Nat}
    {finalState : PaperFactorState}
    (run : GroundedPaperFactorFiniteRun runN sourceStage finalStage
      (correlatedEq66FullRefinementSingletonSourceState
        Dsource hDsource Cmulti def212Constant sourceExact) finalState)
    (middleCount thirdCount : Nat) (firstLoss thirdLoss : ENNReal)
    (final_cardProduct_eq :
      factorCardProduct finalState.factors =
        ((middleCount * thirdCount : Nat) : ENNReal))
    (outerLoss_le_reverse :
      firstLoss * thirdLoss <= cumulativeReverseLoss run.productLedger) :
    CorrelatedEq66LedgerIdentification run.productLedger delta index
      middleCount thirdCount firstLoss thirdLoss
        (cumulativeForwardLoss run.productLedger) :=
  correlatedEq66LedgerIdentification_of_fullRefinementSingletonSource
    Dsource run.productLedger middleCount thirdCount firstLoss thirdLoss
      final_cardProduct_eq outerLoss_le_reverse

/-- Construct the canonical zero-edge grounded run from a genuine selector
witness for this exact source state.  No selector is synthesized. -/
def correlatedEq66FullRefinementSingletonGroundedRunNil
    (Dsource : ActualTubeDatum delta index)
    (hDsource : Dsource.IsAdmissible)
    (Cmulti : CoherentStickyMultiscaleCover
      (fullRefinementDatum Dsource).family)
    (def212Constant : NNReal)
    (sourceExact : ExactScaleDef212Inputs
      Cmulti.base def212Constant)
    {runN stage : Nat}
    (selector : SelectorStageWitness runN
      (correlatedEq66FullRefinementSingletonSourceState
        Dsource hDsource Cmulti def212Constant sourceExact) stage) :
    GroundedPaperFactorFiniteRun runN stage stage
      (correlatedEq66FullRefinementSingletonSourceState
        Dsource hDsource Cmulti def212Constant sourceExact)
      (correlatedEq66FullRefinementSingletonSourceState
        Dsource hDsource Cmulti def212Constant sourceExact) :=
  .nil selector

/-- End-to-end H-row consumer with canonical full-refinement source
provenance.  The count loss and all three source-side ledger identifications
are generated internally.  The only ledger seams are the final factor-card
decomposition and the outer-loss comparison. -/
def groundedRun_normalizedCorrelatedEq66InputsOfHRowFresh_fullRefinementSource
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    {depth : Nat} {epsilon0 beta gamma : Real}
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
    (selectedThird : SameObjectCorrelatedSelectedThirdCertificate
      (delta := delta) U Y Q A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex -> Set Space)
    (hcell : forall p, MeasurableSet (cell p))
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
    (middleScale : NNReal) (middleCount thirdCount : Nat)
    (hThirdCount : thirdCount = Fintype.card coarseIndex)
    (collapsedPrefix outerPrefix firstLoss thirdLoss : ENNReal)
    (final_cardProduct_eq :
      factorCardProduct finalState.factors =
        ((middleCount * thirdCount : Nat) : ENNReal))
    (outerLoss_le_reverse : firstLoss * thirdLoss <=
      cumulativeReverseLoss run.productLedger)
    (hGammaTwo : gamma <= 2)
    (hCollapsed : collapsedPrefix <=
      outerPrefix * A.frozenCoarse.averageMultiplicity)
    (hOuterRowFactor : outerPrefix *
        hRowFreshProp66Factor
          Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M <=
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma)
    (hExponentBudget :
      ((runN : Real) * (uniformityExp + freshExp)) +
          ((runN : Real) * uniformityExp) * (1 - gamma / 2) <=
        3 * P.eta W.stage) :
    {T : NormalizedLongCoreCorrelatedEq66Inputs
        Dsource hDsource Cmulti Sseq P W fine G U Y Q A
          X CKT selectorLoss sourceMass sourceDensity
            massRetentionLoss densityRetentionLoss outputEta //
      T.collapsedPrefix <= T.firstLoss *
        sectionEightScaleCountFrostmanFactor
          delta T.middleScale T.middleCount gamma} := by
  let ledgerId : CorrelatedEq66LedgerIdentification
      run.productLedger delta sourceIndex middleCount thirdCount
        firstLoss thirdLoss (cumulativeForwardLoss run.productLedger) :=
    groundedRun_correlatedEq66LedgerIdentification_of_fullRefinementState
      Dsource hDsource Cmulti sourceDef212Constant sourceExact run
      middleCount thirdCount firstLoss thirdLoss final_cardProduct_eq
        outerLoss_le_reverse
  exact groundedRun_normalizedCorrelatedEq66InputsOfHRowFresh
    Dsource hDsource Cmulti Sseq P W fine G U Y Q A
    X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
      densityRetentionLoss outputEta selectedThird
    Drow Crow q cell hcell selectedCells hmass hactive M correlationLoss Z
      hCoefficientToRow run hUniformityExp hFreshExp hUniformity hFresh
    middleScale middleCount thirdCount hThirdCount collapsedPrefix outerPrefix
    firstLoss thirdLoss (cumulativeForwardLoss run.productLedger) ledgerId
      hGammaTwo hCollapsed hOuterRowFactor hExponentBudget

#print axioms correlatedEq66FullRefinementSourceFactor
#print axioms correlatedEq66FullRefinementSourceFactors
#print axioms correlatedEq66FullRefinementSourceFactors_cardProduct
#print axioms correlatedEq66FullRefinementSourceFactors_radiusProduct
#print axioms correlatedEq66FullRefinementSourceReadiness
#print axioms correlatedEq66FullRefinementSingletonSourceState
#print axioms correlatedEq66FullRefinementSingletonSourceState_factors
#print axioms
  correlatedEq66LedgerIdentification_of_fullRefinementSingletonSource
#print axioms
  groundedRun_correlatedEq66LedgerIdentification_of_fullRefinementState
#print axioms correlatedEq66FullRefinementSingletonGroundedRunNil
#print axioms
  groundedRun_normalizedCorrelatedEq66InputsOfHRowFresh_fullRefinementSource

end
end Family8CorrelatedEq66FullRefinementSingletonSourceProvenanceV1
