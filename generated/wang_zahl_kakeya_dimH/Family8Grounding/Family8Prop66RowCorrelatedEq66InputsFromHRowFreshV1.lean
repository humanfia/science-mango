import Family8Grounding.Family8Prop66Eq66ComposerFromHRowFreshV1
import Family8Grounding.Family8NormalizedLongCoreCorrelatedEq66InputsV1
import Mathlib.Tactic

/-!
# General HRow fresh data at the correlated Equation (66) input seam

One literal `HRowFreshPropertyBundle` is retained through the generalized
Prop. 6.6 composer and into the established correlated Eq. 66 input record.
No row, owner bucket, or fresh subtype is selected in this module.

The proved row endpoint supplies the selected-third coefficient field.  The
coefficient comparison and the existing prefix/count/aggregate power budgets
remain explicit at their first consumer-facing seams.  There is no Equation
(66) triple or dividing-scale conclusion in this file.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8Prop66RowCorrelatedEq66InputsFromHRowFreshV1

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
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66Eq66ComposerFromHRowFreshV1
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

/-! ## Literal general-`tau` row scalars -/

def hRowFreshOwnerCount
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
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) : Nat :=
  (activeSelectedOwnersInCertifiedSlab
    D C q cell hcell selectedCells hmass hactive B.tau B.S).card

/-- The literal plank-occurrence count `N` of the row stored in `B`. -/
def hRowFreshPlankCount
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
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) : Nat :=
  Fintype.card (HRowFreshOccurrence
    D C q cell hcell selectedCells hmass hactive B.tau B.S)

def hRowFreshRowMass
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
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) : ENNReal :=
  (HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.shadingMass

def hRowFreshSelectedMass
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
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) : ENNReal :=
  (HRowFreshSelectedDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
      B.freshSelected).shading.shadingMass

/-! ## Exact M/N/card/mass/factor output from one composer -/

structure HRowFreshTerminalFacts
    (D : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (epsilon beta eta : Real) (M : NNReal)
    (actualThirdAverage correlationLoss : ENNReal)
    (Z : Prop66Eq66ComposerFromHRowFresh
      D C q cell hcell selectedCells hmass hactive epsilon beta eta M
        actualThirdAverage correlationLoss) : Prop where
  owner_occurrence_card_bounds :
    hRowFreshOwnerCount D C q cell hcell selectedCells hmass hactive Z.fresh *
          ownerBucketBranching q ≤
        hRowFreshPlankCount D C q cell hcell selectedCells hmass hactive Z.fresh ∧
      hRowFreshPlankCount D C q cell hcell selectedCells hmass hactive Z.fresh ≤
        hRowFreshOwnerCount D C q cell hcell selectedCells hmass hactive Z.fresh *
          (2 * ownerBucketBranching q)
  fresh_card_retained :
    (hRowFreshPlankCount
        D C q cell hcell selectedCells hmass hactive Z.fresh : ENNReal) ≤
      hRowFreshLoss D C q cell hcell selectedCells hmass hactive
          Z.fresh.tau Z.fresh.S * (Z.fresh.freshSelected.card : ENNReal)
  row_mass_floor :
    (hRowFreshOwnerCount
        D C q cell hcell selectedCells hmass hactive Z.fresh : ENNReal) *
        retainedOwnerHalfAverageFloor C q ≤
      hRowFreshRowMass D C q cell hcell selectedCells hmass hactive Z.fresh
  fresh_mass_retained :
    (eighthNormalizedDatum (HRowFreshSource
        D C q cell hcell selectedCells hmass hactive
          Z.fresh.tau Z.fresh.S)).shading.shadingMass ≤
      hRowFreshLoss D C q cell hcell selectedCells hmass hactive
          Z.fresh.tau Z.fresh.S *
        hRowFreshSelectedMass
          D C q cell hcell selectedCells hmass hactive Z.fresh
  inherited_M : FrostmanThickenedPlankControl
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive Z.fresh.tau Z.fresh.S) M
  branching_le_M_mul_clusteringScale :
    (ownerBucketBranching q : ENNReal) ≤
      (M : ENNReal) * (theta : ENNReal)
  actualThirdAverage_le_rowFactor : actualThirdAverage ≤
    hRowFreshProp66Factor
      D C q cell hcell selectedCells hmass hactive Z.fresh M

theorem HRowFreshTerminalFacts.ofComposer
    {D : ShadedConvexPlankFamily rowIndex a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1)}
    {cellIndex : Type v} {cell : cellIndex → Set Space}
    {hcell : ∀ p, MeasurableSet (cell p)} {selectedCells : Finset cellIndex}
    {hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0}
    {hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty}
    {epsilon beta eta : Real} {M : NNReal}
    {actualThirdAverage correlationLoss : ENNReal}
    (Z : Prop66Eq66ComposerFromHRowFresh
      D C q cell hcell selectedCells hmass hactive epsilon beta eta M
        actualThirdAverage correlationLoss) :
    HRowFreshTerminalFacts
      D C q cell hcell selectedCells hmass hactive epsilon beta eta M
        actualThirdAverage correlationLoss Z where
  owner_occurrence_card_bounds := by
    simpa only [hRowFreshOwnerCount, hRowFreshPlankCount] using
      Z.occurrence_card_bounds
  fresh_card_retained := by
    simpa only [hRowFreshPlankCount, Fintype.card_prod,
      Fintype.card_unit, one_mul] using Z.fresh.fresh_card_retained
  row_mass_floor := by
    simpa only [hRowFreshOwnerCount, hRowFreshRowMass] using Z.row_mass_floor
  fresh_mass_retained := by
    simpa only [hRowFreshSelectedMass] using Z.fresh.fresh_mass_retained
  inherited_M := Z.inherited_thick_control
  branching_le_M_mul_clusteringScale :=
    Z.branching_le_M_mul_clusteringScale
  actualThirdAverage_le_rowFactor := Z.actualThirdAverage_le_prop66Factor

/-! ## First coefficient seam and selected-third constructor -/

def HRowFreshCoefficientBridgeObligation
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
    (M : NNReal) (selectorLoss CKT : ENNReal) : Prop :=
  hRowFreshProp66Factor
      D C q cell hcell selectedCells hmass hactive B M ≤
    selectorLoss * (CKT * volume (unitBallBody : Set Space))

/-- The selected-third coefficient estimate is derived from the one row
composer and the first coefficient bridge; it is not an input. -/
def sameObjectSelectedThirdOfHRowFreshComposer
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
    {epsilonRow betaRow etaRow : Real} (M : NNReal)
    (correlationLoss : ENNReal)
    (Z : Prop66Eq66ComposerFromHRowFresh
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow M
        A.frozenCoarse.averageMultiplicity correlationLoss)
    (hCoefficient : HRowFreshCoefficientBridgeObligation
      Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M
        selectorLoss CKT)
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
    Z.actualThirdAverage_le_prop66Factor.trans hCoefficient
  activeCoarseCard_eq := hCoarseCard
  activeCoarseCard_pos := hCoarsePos
  cardScaleMass_eq := hCardScaleMass
  coefficient_mul_volume_le_cardScale := hCoefficientCardScale
  fourth_cardScaleMass_le_one := hFourthCardScale
  sourceMass_retained := hSourceMass
  sourceDensity_retained := hSourceDensity

/-! ## Direct constructor of the existing normalized correlated inputs -/

/-- Land the exact same row composer at the established pre-DSO input type.
The trailing four inequalities are precisely the earliest scalar seams still
required by that consumer; no `hTriple` or DSO conclusion is accepted. -/
def normalizedCorrelatedEq66InputsOfHRowFreshComposer
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
    {epsilonRow betaRow etaRow : Real} (M : NNReal)
    (correlationLoss : ENNReal)
    (Z : Prop66Eq66ComposerFromHRowFresh
      Drow Crow q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow M
        A.frozenCoarse.averageMultiplicity correlationLoss)
    (hCoefficient : HRowFreshCoefficientBridgeObligation
      Drow Crow q cell hcell selectedCells hmass hactive Z.fresh M
        selectorLoss CKT)
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
  let T := sameObjectSelectedThirdOfHRowFreshComposer
    U Y Q A X CKT selectorLoss sourceMass sourceDensity
      massRetentionLoss densityRetentionLoss outputEta
    Drow Crow q cell hcell selectedCells hmass hactive M correlationLoss Z
      hCoefficient hCoarseCard hCoarsePos hCardScaleMass
      hCoefficientCardScale hFourthCardScale hSourceMass hSourceDensity
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

#print axioms hRowFreshOwnerCount
#print axioms hRowFreshPlankCount
#print axioms hRowFreshRowMass
#print axioms hRowFreshSelectedMass
#print axioms HRowFreshTerminalFacts
#print axioms HRowFreshTerminalFacts.ofComposer
#print axioms HRowFreshCoefficientBridgeObligation
#print axioms sameObjectSelectedThirdOfHRowFreshComposer
#print axioms normalizedCorrelatedEq66InputsOfHRowFreshComposer

end
end Family8Prop66RowCorrelatedEq66InputsFromHRowFreshV1
