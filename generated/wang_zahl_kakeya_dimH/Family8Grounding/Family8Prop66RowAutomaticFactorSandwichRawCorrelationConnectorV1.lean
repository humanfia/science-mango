import Family8Grounding.Family8HRowFreshAutomaticGroundedRunCorrelatedEq66AssemblyV1
import Mathlib.Tactic

/-!
# Raw-correlation replacement for the automatic HRow factor sandwich

The two old sandwich hypotheses point in opposite directions and are stronger
than the fields actually consumed downstream.  This module keeps only the
consumer-facing raw inequalities:

* the actual frozen-third average is below its selected coefficient;
* the displayed correlated coefficient is below
  `correlationLoss * sameRow.averageMultiplicity`.

The first inequality fills the exact selected-third certificate field
directly.  The second is transported through
`B.row_average_le_frostman` and the automatic cross-row theorem to obtain
the honest `M+`/`CF+` factor bound.  The row and fresh subtype are never
reselected.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8FullRefinementActualDatumV1
open Family8HRowFreshAutomaticGroundedRunCorrelatedEq66AssemblyV1
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

/-! ## Earliest raw incidence/correlation seams -/

/-- The exact field needed by the selected-third certificate.  Unlike the
old `hAutomaticCoefficient`, it does not require the whole automatic upper
factor to lie below the selected coefficient. -/
def HRowFreshActualThirdSelectedCoefficientIncidence
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {scale : NNReal} {fine : UniformTubeFamily scale fineIndex}
    {G : ConvexFamily coarseIndex}
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (CKT selectorLoss : ENNReal)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (_B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow) : Prop :=
  A.frozenCoarse.averageMultiplicity ≤
    selectorLoss * (CKT * volume (unitBallBody : Set Space))

/-- The displayed correlated coefficient is controlled by the literal same
row average.  This is the first raw correlation needed in the reverse
consumer direction; it contains no convex-plank factor. -/
def HRowFreshDisplayedCoefficientRowCorrelation
    {delta : NNReal}
    (X selectorLoss : ENNReal) (outputEta : Real)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (correlationLoss : ENNReal) : Prop :=
  selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
    correlationLoss *
      (HRowFreshPlankDatum
        Drow Crow q cell hcell selectedCells hmass hactive
          B.tau B.S).shading.averageMultiplicity

/-! ## Positive producers at the real consumer directions -/

/-- Raw displayed-coefficient correlation, the row Frostman estimate, and
the automatic cross theorem prove the reverse factor inequality. -/
theorem hRowFreshAutomaticCorrelatedCoefficientToFactor_of_rowCorrelation
    {delta : NNReal}
    (X selectorLoss : ENNReal) (outputEta : Real)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl Drow M)
    (correlationLoss : ENNReal) (hcorrelationTop : correlationLoss ≠ ∞)
    (hDisplayed : HRowFreshDisplayedCoefficientRowCorrelation
      (delta := delta) X selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B correlationLoss)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b)
    (hepsilon : 0 ≤ epsilonRow)
    (hbeta0 : 0 ≤ betaRow) (hbeta2 : betaRow ≤ 2) :
    HRowFreshAutomaticCorrelatedCoefficientToFactor
      (delta := delta) X selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B M
        correlationLoss := by
  simpa only [HRowFreshAutomaticCorrelatedCoefficientToFactor,
    HRowFreshDisplayedCoefficientRowCorrelation] using
      actualThirdAverage_le_automaticForwardProp66Factor
        Drow Crow q cell hcell selectedCells hmass hactive B M hthick
          (selectorLoss *
            (128 * (delta : ENNReal) ^ (-outputEta) * X))
          correlationLoss hcorrelationTop hDisplayed hbHalf ha hab
          hepsilon hbeta0 hbeta2

/-- The actual-third/same-row correlation is not an independent seam once
the selected coefficient and displayed coefficient are correlated in their
true consumer directions. -/
theorem hRowFreshActualThirdCorrelation_of_selected_and_displayed
    {delta : NNReal}
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {scale : NNReal} {fine : UniformTubeFamily scale fineIndex}
    {G : ConvexFamily coarseIndex}
    (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (X CKT selectorLoss : ENNReal) (outputEta : Real)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (correlationLoss : ENNReal)
    (hActualSelected : HRowFreshActualThirdSelectedCoefficientIncidence
      Y Q A CKT selectorLoss
      Drow Crow q cell hcell selectedCells hmass hactive B)
    (hCoefficientCardScale :
      CKT * volume (unitBallBody : Set Space) ≤
        128 * (delta : ENNReal) ^ (-outputEta) * X)
    (hDisplayed : HRowFreshDisplayedCoefficientRowCorrelation
      (delta := delta) X selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B correlationLoss) :
    HRowFreshActualThirdCorrelationObligation
      Drow Crow q cell hcell selectedCells hmass hactive B
        A.frozenCoarse.averageMultiplicity correlationLoss := by
  unfold HRowFreshActualThirdCorrelationObligation
  calc
    A.frozenCoarse.averageMultiplicity ≤
        selectorLoss * (CKT * volume (unitBallBody : Set Space)) :=
      hActualSelected
    _ ≤ selectorLoss *
        (128 * (delta : ENNReal) ^ (-outputEta) * X) :=
      mul_le_mul' le_rfl hCoefficientCardScale
    _ ≤ correlationLoss *
        (HRowFreshPlankDatum
          Drow Crow q cell hcell selectedCells hmass hactive
            B.tau B.S).shading.averageMultiplicity := hDisplayed

/-- Construct the exact same-object selected-third certificate directly from
the raw actual-third incidence inequality. -/
def sameObjectSelectedThirdOfHRowFreshRawCoefficientIncidence
    {delta : NNReal}
    {fineIndex coarseIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    [Fintype coarseIndex] [DecidableEq coarseIndex]
    {scale rho : NNReal} {fine : UniformTubeFamily scale fineIndex}
    {G : ConvexFamily coarseIndex}
    (U : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (Q : ConvexFactorization fine.bodyFamily G)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y 1)
    (X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss : ENNReal)
    (outputEta : Real)
    (Drow : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (Crow : MutualThickeningClustering Drow theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily Drow Crow q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      Drow Crow q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (hActualSelected : HRowFreshActualThirdSelectedCoefficientIncidence
      Y Q A CKT selectorLoss
      Drow Crow q cell hcell selectedCells hmass hactive B)
    (hCoarseCard : Fintype.card coarseIndex = U.coarseCard)
    (hCoarsePos : 0 < Fintype.card coarseIndex)
    (hCardScaleMass :
      X = (Fintype.card coarseIndex : ENNReal) * (rho : ENNReal) ^ (2 : Nat))
    (hCoefficientCardScale :
      CKT * volume (unitBallBody : Set Space) ≤
        128 * (delta : ENNReal) ^ (-outputEta) * X)
    (hFourthCardScale : (rho : ENNReal) ^ (4 : Nat) * X ≤ 1)
    (hSourceMass : sourceMass ≤
      massRetentionLoss * shadingMassOn Y U.activeFine)
    (hSourceDensity : densityRetentionLoss * sourceDensity ≤
      Y.shadingDensity) :
    SameObjectCorrelatedSelectedThirdCertificate (delta := delta)
      U Y Q A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta where
  actualThirdAverage := A.frozenCoarse.averageMultiplicity
  actualThirdAverage_eq := rfl
  actualThirdAverage_le_coefficient := hActualSelected
  activeCoarseCard_eq := hCoarseCard
  activeCoarseCard_pos := hCoarsePos
  cardScaleMass_eq := hCardScaleMass
  coefficient_mul_volume_le_cardScale := hCoefficientCardScale
  fourth_cardScaleMass_le_one := hFourthCardScale
  sourceMass_retained := hSourceMass
  sourceDensity_retained := hSourceDensity

/-! ## Grounded assembly without either factor-sandwich hypothesis -/

/-- Grounded correlated Eq. 6.6 inputs from the two raw inequalities actually
consumed downstream.

The selected-third certificate is built directly from the actual-third
incidence inequality.  The displayed coefficient is transported through the
literal same-row average, `B.row_average_le_frostman`, and the automatic
cross-row theorem.  Thus neither direction of the old factor sandwich is an
input, and all automatic bounds use the same `B`, `M+`, and `CF+`. -/
def groundedRun_normalizedCorrelatedEq66InputsOfHRowFreshAutomaticRawCorrelations
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
    (hActualSelected : HRowFreshActualThirdSelectedCoefficientIncidence
      Y Q A CKT selectorLoss
      Drow Crow q cell hcell selectedCells hmass hactive B)
    (hDisplayed : HRowFreshDisplayedCoefficientRowCorrelation
      (delta := delta) X selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B correlationLoss)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b)
    (hepsilon : 0 ≤ epsilonRow)
    (hbeta0 : 0 ≤ betaRow) (hbeta2 : betaRow ≤ 2)
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
    sameObjectSelectedThirdOfHRowFreshRawCoefficientIncidence
      U Y Q A X CKT selectorLoss sourceMass sourceDensity
        massRetentionLoss densityRetentionLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B
        hActualSelected hCoarseCard hCoarsePos hCardScaleMass
        hCoefficientCardScale hFourthCardScale hSourceMass hSourceDensity
  let rowFactor :=
    hRowFreshAutomaticForwardProp66Factor
      Drow Crow q cell hcell selectedCells hmass hactive B M correlationLoss
  have hThirdToRowAvg : HRowFreshActualThirdCorrelationObligation
      Drow Crow q cell hcell selectedCells hmass hactive B
        A.frozenCoarse.averageMultiplicity correlationLoss :=
    hRowFreshActualThirdCorrelation_of_selected_and_displayed
      Y Q A X CKT selectorLoss outputEta
      Drow Crow q cell hcell selectedCells hmass hactive B correlationLoss
        hActualSelected hCoefficientCardScale hDisplayed
  have hActualToFactor :
      A.frozenCoarse.averageMultiplicity ≤ rowFactor := by
    simpa only [rowFactor] using
      actualThirdAverage_le_automaticForwardProp66Factor
        Drow Crow q cell hcell selectedCells hmass hactive B M hthick
          A.frozenCoarse.averageMultiplicity correlationLoss
          hcorrelationTop hThirdToRowAvg hbHalf ha hab
          hepsilon hbeta0 hbeta2
  have hCoefficientToFactor :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
        rowFactor := by
    simpa only [rowFactor,
      HRowFreshAutomaticCorrelatedCoefficientToFactor] using
      hRowFreshAutomaticCorrelatedCoefficientToFactor_of_rowCorrelation
        X selectorLoss outputEta
        Drow Crow q cell hcell selectedCells hmass hactive B M hthick
          correlationLoss hcorrelationTop hDisplayed hbHalf ha hab
          hepsilon hbeta0 hbeta2
  exact groundedRun_normalizedCorrelatedEq66InputsOfFactorSandwich
    Dsource hDsource Cmulti Sseq P W fine G U Y Q A
      X CKT selectorLoss sourceMass sourceDensity massRetentionLoss
        densityRetentionLoss outputEta selectedThird rowFactor
      hActualToFactor hCoefficientToFactor run hUniformityExp hFreshExp
      hUniformity hFresh middleScale middleCount thirdCount hThirdCount
      collapsedPrefix outerPrefix firstLoss thirdLoss countLoss ledgerId
      hGammaTwo hCollapsed hOuterFactor hExponentBudget

#print axioms HRowFreshActualThirdSelectedCoefficientIncidence
#print axioms HRowFreshDisplayedCoefficientRowCorrelation
#print axioms
  hRowFreshAutomaticCorrelatedCoefficientToFactor_of_rowCorrelation
#print axioms hRowFreshActualThirdCorrelation_of_selected_and_displayed
#print axioms sameObjectSelectedThirdOfHRowFreshRawCoefficientIncidence
#print axioms
  groundedRun_normalizedCorrelatedEq66InputsOfHRowFreshAutomaticRawCorrelations

end
end Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
