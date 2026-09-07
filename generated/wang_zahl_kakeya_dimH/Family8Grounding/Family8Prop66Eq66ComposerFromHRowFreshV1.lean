import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8Prop66Eq66ComposerFromHRowFreshV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8ActiveCoarseCanonicalFrostmanXLowerV3
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Prop. 6.6 / Eq. 66 composer from one existing HRow fresh bundle

This module never selects a row or a fresh subtype.  Its sole object input is
an already constructed `HRowFreshPropertyBundle`; every scalar and structural
field below is projected from that exact row and exact selected finset.
-/

/-- The exact same-row Prop. 6.6 factor carried by a generalized HRow bundle. -/
def hRowFreshProp66Factor
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) : ENNReal :=
  convexPlankFrostmanFactor
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive B.tau B.S)
    epsilon beta
    (hRowFreshCanonicalFrostmanConstant
      D C q cell hcell selectedCells hmass hactive B.tau B.S) M

/-- Explicit correlation of the downstream actual-third scalar with the
average multiplicity of the exact row stored in `B`. -/
def HRowFreshActualThirdCorrelationObligation
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (actualThirdAverage correlationLoss : ENNReal) : Prop :=
  actualThirdAverage ≤ correlationLoss *
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity

/-- Explicit aggregation from the already proved same-selected Frostman
bound to the exact row convex-plank factor. -/
def HRowFreshCrossRowAggregationObligation
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (correlationLoss : ENNReal) : Prop :=
  correlationLoss *
      (hRowFreshLoss
          D C q cell hcell selectedCells hmass hactive B.tau B.S *
        frostmanMultiplicityRHS (b / 8)
          (HRowFreshSelectedDatum
            D C q cell hcell selectedCells hmass hactive B.tau B.S
              B.freshSelected).actualFamilyVolume epsilon beta) ≤
    hRowFreshProp66Factor
      D C q cell hcell selectedCells hmass hactive B M

/-- A nonempty row at an arbitrary certified scale still contains a heavy
selected owner. Hence the original clustering gives its branching cap at
the clustering scale `theta`; no equality `B.tau = theta` is asserted. -/
theorem hRowFresh_branching_le_M_mul_clusteringScale
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (M : NNReal) (hthick : FrostmanThickenedPlankControl D M)
    (hratio : a / b ≤ theta) (htheta : theta ≤ 1) :
    (ownerBucketBranching q : ENNReal) ≤
      (M : ENNReal) * (theta : ENNReal) := by
  obtain ⟨s, hsRow⟩ := B.hrow
  have hsBucket : s.1 ∈ selectedOwnerLogBucket C q :=
    (mem_heavyRetainedOwners C q s.1).1 s.2 |>.1
  calc
    (ownerBucketBranching q : ENNReal) ≤
        ((ownerFiber C s.1).card : ENNReal) := by
      exact_mod_cast (selectedOwnerLogBucket_card_bounds C q hsBucket).1
    _ ≤ (M : ENNReal) * (theta : ENNReal) :=
      ownerFiber_card_le D M theta C hthick hratio htheta s.1

/-- Thin same-object composer. The `fresh` field is the unique pre-existing
bundle; no row or subtype selection occurs in this structure or producer. -/
structure Prop66Eq66ComposerFromHRowFresh
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (epsilon beta eta : Real) (M : NNReal)
    (actualThirdAverage correlationLoss : ENNReal) where
  fresh : HRowFreshPropertyBundle
    D C q cell hcell selectedCells hmass hactive epsilon beta eta
  row_mass_identity :
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S).shading.shadingMass =
      ∑ s : ActiveSelectedOwnerRow
          D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S,
        ownerFiberMass C s.1.1
  occurrence_card_identity :
    Fintype.card (HRowFreshOccurrence
      D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S) =
      ∑ s : ActiveSelectedOwnerRow
          D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S,
        (ownerFiber C s.1.1).card
  row_mass_floor :
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S).card : ENNReal) *
        retainedOwnerHalfAverageFloor C q ≤
      (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S).shading.shadingMass
  occurrence_card_bounds :
    (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S).card *
          ownerBucketBranching q ≤
        Fintype.card (HRowFreshOccurrence
          D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S) ∧
    Fintype.card (HRowFreshOccurrence
        D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S) ≤
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S).card *
          (2 * ownerBucketBranching q)
  inherited_thick_control : FrostmanThickenedPlankControl
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive fresh.tau fresh.S) M
  branching_le_M_mul_clusteringScale :
    (ownerBucketBranching q : ENNReal) ≤
      (M : ENNReal) * (theta : ENNReal)
  actualThirdAverage_correlation : HRowFreshActualThirdCorrelationObligation
    D C q cell hcell selectedCells hmass hactive fresh
      actualThirdAverage correlationLoss
  crossRowAggregation : HRowFreshCrossRowAggregationObligation
    D C q cell hcell selectedCells hmass hactive fresh M correlationLoss

/-- Deterministic wrapper of one existing HRow fresh bundle. -/
def Prop66Eq66ComposerFromHRowFresh.ofBundle
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {cellIndex : Type v} {cell : cellIndex → Set Space}
    {hcell : ∀ p, MeasurableSet (cell p)} {selectedCells : Finset cellIndex}
    {hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0}
    {hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty}
    {epsilon beta eta : Real} {M : NNReal}
    {actualThirdAverage correlationLoss : ENNReal}
    (hthick : FrostmanThickenedPlankControl D M)
    (hratio : a / b ≤ theta) (htheta : theta ≤ 1)
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive epsilon beta eta)
    (hActual : HRowFreshActualThirdCorrelationObligation
      D C q cell hcell selectedCells hmass hactive B
        actualThirdAverage correlationLoss)
    (hCross : HRowFreshCrossRowAggregationObligation
      D C q cell hcell selectedCells hmass hactive B M correlationLoss) :
    Prop66Eq66ComposerFromHRowFresh
      D C q cell hcell selectedCells hmass hactive epsilon beta eta M
        actualThirdAverage correlationLoss where
  fresh := B
  row_mass_identity := activeSelectedOwnerRowPlankDatum_shadingMass
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  occurrence_card_identity := activeSelectedOwnerRowOccurrence_card
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  row_mass_floor := activeSelectedOwnerRow_card_mul_floor_le_shadingMass
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  occurrence_card_bounds := activeSelectedOwnerRowOccurrence_card_bounds
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  inherited_thick_control :=
    activeSelectedOwnerRowPlankDatum_frostmanThickenedPlankControl
      D C q cell hcell selectedCells hmass hactive B.tau B.S M hthick
  branching_le_M_mul_clusteringScale :=
    hRowFresh_branching_le_M_mul_clusteringScale
      D C q cell hcell selectedCells hmass hactive B M hthick hratio htheta
  actualThirdAverage_correlation := hActual
  crossRowAggregation := hCross

namespace Prop66Eq66ComposerFromHRowFresh

/-- Scalar endpoint for the exact row and exact selected subtype stored in
the composer. -/
theorem actualThirdAverage_le_prop66Factor
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
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
    actualThirdAverage ≤ hRowFreshProp66Factor
      D C q cell hcell selectedCells hmass hactive Z.fresh M := by
  calc
    actualThirdAverage ≤ correlationLoss *
        (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive
            Z.fresh.tau Z.fresh.S).shading.averageMultiplicity := by
      simpa only [HRowFreshActualThirdCorrelationObligation] using
        Z.actualThirdAverage_correlation
    _ ≤ correlationLoss *
        (hRowFreshLoss
            D C q cell hcell selectedCells hmass hactive
              Z.fresh.tau Z.fresh.S *
          frostmanMultiplicityRHS (b / 8)
            (HRowFreshSelectedDatum
              D C q cell hcell selectedCells hmass hactive
                Z.fresh.tau Z.fresh.S
                Z.fresh.freshSelected).actualFamilyVolume epsilon beta) := by
      gcongr
      exact Z.fresh.row_average_le_frostman
    _ ≤ hRowFreshProp66Factor
        D C q cell hcell selectedCells hmass hactive Z.fresh M := by
      simpa only [HRowFreshCrossRowAggregationObligation] using
        Z.crossRowAggregation

end Prop66Eq66ComposerFromHRowFresh

#print axioms hRowFresh_branching_le_M_mul_clusteringScale
#print axioms Prop66Eq66ComposerFromHRowFresh
#print axioms Prop66Eq66ComposerFromHRowFresh.ofBundle
#print axioms Prop66Eq66ComposerFromHRowFresh.actualThirdAverage_le_prop66Factor

end
end Family8Prop66Eq66ComposerFromHRowFreshV1
