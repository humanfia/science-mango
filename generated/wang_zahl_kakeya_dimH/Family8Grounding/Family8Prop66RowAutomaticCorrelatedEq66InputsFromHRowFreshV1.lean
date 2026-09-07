import Family8Grounding.Family8Prop66RowAutomaticForwardThickeningConnectorV1
import Family8Grounding.Family8Prop66RowCorrelatedEq66InputsFromHRowFreshV1
import Mathlib.Tactic

/-!
# Automatic HRow Prop. 6.6 factor at the correlated Equation (66) seam

This module connects one literal `HRowFreshPropertyBundle` to the existing
same-object selected-third certificate and normalized correlated Eq. 66 input
record.  The row, slab, and fresh subtype are never reselected.

The two scalar budgets formerly named `hForward` and `hCopy` are discharged
by the honest monotone choices

* `M+ = max M ((effectiveLoss / (a / b)).toNNReal)`;
* `CF+ = max canonicalCF (2 * M+)`.

Consequently, the coefficient bridge below is explicitly stated at the
automatic augmented factor.  Nothing in this file identifies that factor
with the smaller original-`M`, canonical-`CF` factor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8Prop66RowAutomaticCorrelatedEq66InputsFromHRowFreshV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8FullRefinementActualDatumV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCorrelatedEq66InputsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowAutomaticForwardThickeningConnectorV1
open Family8SameObjectCorrelatedSelectedThirdCertificateV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
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

/-- The first downstream coefficient comparison at the honest automatic
`M+`/`CF+` factor. -/
def HRowFreshAutomaticCoefficientBridgeObligation
    (D : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (correlationLoss selectorLoss CKT : ENNReal) : Prop :=
  hRowFreshAutomaticForwardProp66Factor
      D C q cell hcell selectedCells hmass hactive B M correlationLoss ≤
    selectorLoss * (CKT * volume (unitBallBody : Set Space))

/-- Produce the selected-third certificate directly from the same HRow bundle.
There are no `hForward` or `hCopy` inputs: both are proved by the automatic
monotone choices before this constructor is called. -/
def sameObjectSelectedThirdOfHRowFreshAutomaticForward
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
    (M : NNReal) (hthick : FrostmanThickenedPlankControl Drow M)
    (correlationLoss : ENNReal) (hcorrelationTop : correlationLoss ≠ ∞)
    (hThirdToRowAvg : HRowFreshActualThirdCorrelationObligation
      Drow Crow q cell hcell selectedCells hmass hactive B
        A.frozenCoarse.averageMultiplicity correlationLoss)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b)
    (hepsilon : 0 ≤ epsilonRow)
    (hbeta0 : 0 ≤ betaRow) (hbeta2 : betaRow ≤ 2)
    (hCoefficient : HRowFreshAutomaticCoefficientBridgeObligation
      Drow Crow q cell hcell selectedCells hmass hactive B M
        correlationLoss selectorLoss CKT)
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
  actualThirdAverage_le_coefficient :=
    (actualThirdAverage_le_automaticForwardProp66Factor
      Drow Crow q cell hcell selectedCells hmass hactive B M hthick
        A.frozenCoarse.averageMultiplicity correlationLoss
        hcorrelationTop hThirdToRowAvg hbHalf ha hab hepsilon hbeta0 hbeta2).trans
      hCoefficient
  activeCoarseCard_eq := hCoarseCard
  activeCoarseCard_pos := hCoarsePos
  cardScaleMass_eq := hCardScaleMass
  coefficient_mul_volume_le_cardScale := hCoefficientCardScale
  fourth_cardScaleMass_le_one := hFourthCardScale
  sourceMass_retained := hSourceMass
  sourceDensity_retained := hSourceDensity

/-- Direct constructor of the established normalized correlated Eq. 66 input
record.  It consumes the automatic selected-third certificate above, while
leaving exactly the pre-existing prefix/count/aggregate seams explicit. -/
def normalizedCorrelatedEq66InputsOfHRowFreshAutomaticForward
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
    (hThirdToRowAvg : HRowFreshActualThirdCorrelationObligation
      Drow Crow q cell hcell selectedCells hmass hactive B
        A.frozenCoarse.averageMultiplicity correlationLoss)
    (hbHalf : b ≤ (2 : NNReal)⁻¹)
    (ha : 0 < a) (hab : a ≤ b)
    (hepsilon : 0 ≤ epsilonRow)
    (hbeta0 : 0 ≤ betaRow) (hbeta2 : betaRow ≤ 2)
    (hCoefficient : HRowFreshAutomaticCoefficientBridgeObligation
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
    (middleScale : NNReal) (middleCount thirdCount : Nat)
    (hThirdCount : thirdCount = Fintype.card coarseIndex)
    (collapsedPrefix outerPrefix firstLoss thirdLoss countLoss : ENNReal)
    (hCollapsed : collapsedPrefix ≤
      outerPrefix * A.frozenCoarse.averageMultiplicity)
    (hCorrelatedPower : outerPrefix *
        (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) ≤
      firstLoss * sectionEightScaleCountFrostmanFactor
        delta middleScale middleCount gamma)
    (hCount : ((middleCount * thirdCount : Nat) : ENNReal) ≤
      countLoss * (Fintype.card sourceIndex : ENNReal))
    (hAggregate : (firstLoss * thirdLoss) *
        countLoss ^ (1 - gamma / 2) ≤
      (delta : ENNReal) ^ (-3 * P.eta W.stage)) :
    NormalizedLongCoreCorrelatedEq66Inputs
      Dsource hDsource Cmulti Sseq P W fine G U Y Q A
        X CKT selectorLoss sourceMass sourceDensity
          massRetentionLoss densityRetentionLoss outputEta := by
  let T := sameObjectSelectedThirdOfHRowFreshAutomaticForward
    U Y Q A X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss outputEta
    Drow Crow q cell hcell selectedCells hmass hactive B M hthick
      correlationLoss hcorrelationTop hThirdToRowAvg hbHalf ha hab
      hepsilon hbeta0 hbeta2 hCoefficient hCoarseCard hCoarsePos
      hCardScaleMass hCoefficientCardScale hFourthCardScale
      hSourceMass hSourceDensity
  exact {
    selectedThird := T
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
      change collapsedPrefix ≤ outerPrefix * A.frozenCoarse.averageMultiplicity
      exact hCollapsed
    correlatedPrefixBudget := hCorrelatedPower
    hCount := hCount
    hAggregateLoss := hAggregate }

#print axioms HRowFreshAutomaticCoefficientBridgeObligation
#print axioms sameObjectSelectedThirdOfHRowFreshAutomaticForward
#print axioms normalizedCorrelatedEq66InputsOfHRowFreshAutomaticForward

end
end Family8Prop66RowAutomaticCorrelatedEq66InputsFromHRowFreshV1
