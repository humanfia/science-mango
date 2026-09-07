import Family8Grounding.Family8Prop66RowCrossScaleAggregationV1
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Mathlib.Tactic

/-!
# Honest high/low gate for the H-row forward-power budget

The mass-retaining logarithmic owner bucket does not by itself force its
branching number to dominate the later fresh-selection loss.  This file keeps
that distinction explicit.  The high branch is exactly the existing
`HRowFreshForwardPowerBudget`; on the complementary branch the row average is
bounded directly by the literal row cardinality and hence by twice the owner
count times the effective loss.

No convex-plank hypothesis or cross-row conclusion is assumed here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowFreshForwardPowerGateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8FrostmanOneFromPointwisePackingV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8Prop66Eq66ComposerFromHRowFreshV1
open Family8Prop66RowCrossScaleAggregationV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The honest complementary branch to `HRowFreshForwardPowerBudget`. -/
def HRowFreshLowForwardPowerBranch
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
    (correlationLoss : ENNReal) : Prop :=
  (ownerBucketBranching q : ENNReal) <
    hRowFreshEffectiveLoss
      D C q cell hcell selectedCells hmass hactive B correlationLoss

/-- Every already chosen H-row lies in exactly the high branch needed by the
existing aggregation theorem or in its strict low-branch complement. -/
theorem hRowFresh_forwardPowerBudget_or_lowForwardBranch
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
    (correlationLoss : ENNReal) :
    HRowFreshForwardPowerBudget
        D C q cell hcell selectedCells hmass hactive B correlationLoss ∨
      HRowFreshLowForwardPowerBranch
        D C q cell hcell selectedCells hmass hactive B correlationLoss := by
  exact le_or_gt
    (hRowFreshEffectiveLoss
      D C q cell hcell selectedCells hmass hactive B correlationLoss)
    (ownerBucketBranching q : ENNReal)

/-- The selected property row has average multiplicity at most its literal
occurrence-cardinality envelope. -/
theorem hRowFreshPlankDatum_averageMultiplicity_le_rowCard_mul_twoBranching
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
      D C q cell hcell selectedCells hmass hactive epsilon beta eta) :
    (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity ≤
      ((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selectedCells hmass hactive B.tau B.S).card *
        (2 * ownerBucketBranching q) : Nat) := by
  calc
    (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity ≤
        (Fintype.card (HRowFreshOccurrence
          D C q cell hcell selectedCells hmass hactive B.tau B.S) : ENNReal) :=
      averageMultiplicity_le_indexCard _
    _ ≤ ((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selectedCells hmass hactive B.tau B.S).card *
        (2 * ownerBucketBranching q) : Nat) := by
      exact_mod_cast
        (activeSelectedOwnerRowOccurrence_card_bounds
          D C q cell hcell selectedCells hmass hactive B.tau B.S).2

/-- In the strict low branch, replace the owner branching number in the
cardinality bound by the effective loss.  This is the direct bound available
before any small-scale power absorption. -/
theorem hRowFreshPlankDatum_averageMultiplicity_le_ownerCount_mul_two_mul_effectiveLoss
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
    (correlationLoss : ENNReal)
    (hlow : HRowFreshLowForwardPowerBranch
      D C q cell hcell selectedCells hmass hactive B correlationLoss) :
    (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity ≤
      (((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selectedCells hmass hactive B.tau B.S).card : ENNReal) * 2) *
        hRowFreshEffectiveLoss
          D C q cell hcell selectedCells hmass hactive B correlationLoss := by
  have hcard := hRowFreshPlankDatum_averageMultiplicity_le_rowCard_mul_twoBranching
    D C q cell hcell selectedCells hmass hactive B
  calc
    (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity ≤
      ((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selectedCells hmass hactive B.tau B.S).card *
        (2 * ownerBucketBranching q) : Nat) := hcard
    _ = (((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selectedCells hmass hactive B.tau B.S).card : ENNReal) * 2) *
        (ownerBucketBranching q : ENNReal) := by
      norm_num [Nat.cast_mul]
      ac_rfl
    _ ≤ (((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selectedCells hmass hactive B.tau B.S).card : ENNReal) * 2) *
        hRowFreshEffectiveLoss
          D C q cell hcell selectedCells hmass hactive B correlationLoss := by
      exact mul_le_mul' le_rfl (le_of_lt hlow)

/-- The same low-branch cardinality estimate after applying the downstream
actual-third/row correlation.  This isolates the exact scalar which a low
branch endpoint still has to absorb. -/
theorem hRowFresh_actualThirdAverage_le_correlationLoss_mul_ownerCount_mul_two_mul_effectiveLoss
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
    (actualThirdAverage correlationLoss : ENNReal)
    (hActual : HRowFreshActualThirdCorrelationObligation
      D C q cell hcell selectedCells hmass hactive B
        actualThirdAverage correlationLoss)
    (hlow : HRowFreshLowForwardPowerBranch
      D C q cell hcell selectedCells hmass hactive B correlationLoss) :
    actualThirdAverage ≤
      correlationLoss *
        ((((activeSelectedOwnersInCertifiedSlab
            D C q cell hcell selectedCells hmass hactive B.tau B.S).card : ENNReal) * 2) *
          hRowFreshEffectiveLoss
            D C q cell hcell selectedCells hmass hactive B correlationLoss) := by
  calc
    actualThirdAverage ≤
        correlationLoss *
          (HRowFreshPlankDatum
            D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.averageMultiplicity :=
      hActual
    _ ≤ correlationLoss *
        ((((activeSelectedOwnersInCertifiedSlab
            D C q cell hcell selectedCells hmass hactive B.tau B.S).card : ENNReal) * 2) *
          hRowFreshEffectiveLoss
            D C q cell hcell selectedCells hmass hactive B correlationLoss) := by
      exact mul_le_mul' le_rfl
        (hRowFreshPlankDatum_averageMultiplicity_le_ownerCount_mul_two_mul_effectiveLoss
          D C q cell hcell selectedCells hmass hactive B correlationLoss hlow)

/-- Low-branch reduction using the literal owner mass floor.  Everything in
this implication except `hMassBudget` is already furnished by the selected
H-row.  Consequently `hMassBudget` is a division-free statement of the true
remaining low-branch incidence/core inequality, rather than the false global
requirement `effectiveLoss ≤ ownerBucketBranching`. -/
theorem hRowFresh_actualThirdAverage_le_of_lowForwardBranch_and_rowMassBudget
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
    (actualThirdAverage correlationLoss target : ENNReal)
    (hActual : HRowFreshActualThirdCorrelationObligation
      D C q cell hcell selectedCells hmass hactive B
        actualThirdAverage correlationLoss)
    (hlow : HRowFreshLowForwardPowerBranch
      D C q cell hcell selectedCells hmass hactive B correlationLoss)
    (hMassBudget :
      (correlationLoss *
          (2 * hRowFreshEffectiveLoss
            D C q cell hcell selectedCells hmass hactive B correlationLoss)) *
        (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive B.tau B.S).shading.shadingMass ≤
      retainedOwnerHalfAverageFloor C q * target) :
    actualThirdAverage ≤ target := by
  let owners := activeSelectedOwnersInCertifiedSlab
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let rowD := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let effectiveLoss := hRowFreshEffectiveLoss
    D C q cell hcell selectedCells hmass hactive B correlationLoss
  let floor := retainedOwnerHalfAverageFloor C q
  have hbucketMass0 :
      (∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s) ≠ 0 := by
    intro hzero
    apply hmass
    rw [retainedOwnerPlankFamily_shadingMass]
    exact hzero
  have hfloor0 : floor ≠ 0 := by
    dsimp only [floor, retainedOwnerHalfAverageFloor]
    apply ENNReal.div_ne_zero.mpr
    exact ⟨hbucketMass0, ENNReal.mul_ne_top
      (by norm_num) (ENNReal.natCast_ne_top _)⟩
  have hmassPos :
      0 < (retainedOwnerPlankFamily D C q).shading.shadingMass :=
    bot_lt_iff_ne_bot.mpr hmass
  obtain ⟨owner, howner⟩ :=
    heavyRetainedOwners_nonempty_of_retainedMass_pos D C q hmassPos
  have hfloorTop : floor ≠ ∞ := by
    dsimp only [floor]
    exact ne_top_of_le_ne_top (ownerFiberMass_ne_top C owner)
      (retainedOwnerHalfAverageFloor_le_ownerFiberMass C q howner)
  have hrowFloor : (owners.card : ENNReal) * floor ≤ rowD.shading.shadingMass := by
    simpa only [owners, rowD, floor] using
      activeSelectedOwnerRow_card_mul_floor_le_shadingMass
        D C q cell hcell selectedCells hmass hactive B.tau B.S
  have hlowActual : actualThirdAverage ≤
      correlationLoss * (((owners.card : ENNReal) * 2) * effectiveLoss) := by
    simpa only [owners, effectiveLoss] using
      hRowFresh_actualThirdAverage_le_correlationLoss_mul_ownerCount_mul_two_mul_effectiveLoss
        D C q cell hcell selectedCells hmass hactive B
          actualThirdAverage correlationLoss hActual hlow
  apply (ENNReal.mul_le_mul_iff_right hfloor0 hfloorTop).1
  calc
    floor * actualThirdAverage = actualThirdAverage * floor := mul_comm _ _
    _ ≤
        (correlationLoss * (((owners.card : ENNReal) * 2) * effectiveLoss)) * floor :=
      mul_le_mul' hlowActual le_rfl
    _ = (correlationLoss * (2 * effectiveLoss)) *
        ((owners.card : ENNReal) * floor) := by ac_rfl
    _ ≤ (correlationLoss * (2 * effectiveLoss)) * rowD.shading.shadingMass :=
      mul_le_mul' le_rfl hrowFloor
    _ ≤ floor * target := by
      simpa only [rowD, effectiveLoss, floor] using hMassBudget

#print axioms hRowFresh_forwardPowerBudget_or_lowForwardBranch
#print axioms
  hRowFreshPlankDatum_averageMultiplicity_le_rowCard_mul_twoBranching
#print axioms
  hRowFreshPlankDatum_averageMultiplicity_le_ownerCount_mul_two_mul_effectiveLoss
#print axioms
  hRowFresh_actualThirdAverage_le_correlationLoss_mul_ownerCount_mul_two_mul_effectiveLoss
#print axioms
  hRowFresh_actualThirdAverage_le_of_lowForwardBranch_and_rowMassBudget

end
end Family8HRowFreshForwardPowerGateV1
