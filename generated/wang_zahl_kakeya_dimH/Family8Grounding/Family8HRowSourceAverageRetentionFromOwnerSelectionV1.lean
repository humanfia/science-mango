import Family8Grounding.Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
import Mathlib.Tactic

/-!
# Source-average retention on the literal selected H-row

This module isolates the finite incidence step which is independent of the
later Frostman estimate.  A logarithmic owner bucket is selected before the
certified slab row.  Every owner in the final row is heavy, hence its complete
owner fibre has at least half the average bucket mass.  Consequently the
source mass is controlled by the mass of the exact row stored in the supplied
`HRowFreshPropertyBundle`.  Since that row is a literal restriction of the
source shading, its shaded union is contained in the source shaded union, so
the same comparison holds for average multiplicity.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowSourceAverageRetentionFromOwnerSelectionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- The exact finite loss needed to pass from a selected owner bucket to one
heavy certified row. -/
def ownerBucketToHRowLoss
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1)) : ENNReal :=
  2 * ((selectedOwnerLogBucket C q).card : ENNReal)

/-- The complete-owner-fibre row is a literal shading restriction of `D`.
Only the shaded-union inclusion used by the average consumer is exported. -/
theorem hRowFreshPlankDatum_shadedUnion_subset_source
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive tau S).shading.shadedUnion ⊆
        D.shading.shadedUnion := by
  intro x hx
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨p.2.1, hp⟩

/-- The owner half-average floor converts the retained bucket mass into the
mass of the exact row chosen in `B`. -/
theorem retainedOwnerPlankFamily_mass_le_ownerBucketToHRowLoss_mul_rowMass
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
    (retainedOwnerPlankFamily D C q).shading.shadingMass ≤
      ownerBucketToHRowLoss C q *
        (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive
            B.tau B.S).shading.shadingMass := by
  let bucketMass : ENNReal :=
    ∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s
  let denominator : ENNReal :=
    2 * ((selectedOwnerLogBucket C q).card : ENNReal)
  have hbucketMass0 : bucketMass ≠ 0 := by
    intro hzero
    apply hmass
    rw [retainedOwnerPlankFamily_shadingMass]
    exact hzero
  have hbucketNonempty : (selectedOwnerLogBucket C q).Nonempty := by
    by_contra hempty
    have hnil : selectedOwnerLogBucket C q = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hbucketMass0
    simp [bucketMass, hnil]
  have hdenominator0 : denominator ≠ 0 := by
    unfold denominator
    exact mul_ne_zero (by norm_num) (by
      exact_mod_cast (Finset.card_ne_zero.mpr hbucketNonempty))
  have hdenominatorTop : denominator ≠ ∞ := by
    unfold denominator
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
  have hfloor_le_rowMass : retainedOwnerHalfAverageFloor C q ≤
      (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive
          B.tau B.S).shading.shadingMass := by
    have hrowFloor := activeSelectedOwnerRow_card_mul_floor_le_shadingMass
      D C q cell hcell selectedCells hmass hactive B.tau B.S
    have hcardOne : (1 : ENNReal) ≤
        ((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selectedCells hmass hactive
            B.tau B.S).card : ENNReal) := by
      exact_mod_cast (Finset.one_le_card.mpr B.hrow)
    calc
      retainedOwnerHalfAverageFloor C q =
          1 * retainedOwnerHalfAverageFloor C q := by simp
      _ ≤ ((activeSelectedOwnersInCertifiedSlab
            D C q cell hcell selectedCells hmass hactive
              B.tau B.S).card : ENNReal) *
            retainedOwnerHalfAverageFloor C q :=
        mul_le_mul' hcardOne le_rfl
      _ ≤ (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive
            B.tau B.S).shading.shadingMass := hrowFloor
  have hbucketIdentity : bucketMass =
      denominator * retainedOwnerHalfAverageFloor C q := by
    rw [retainedOwnerHalfAverageFloor]
    change bucketMass = denominator * (bucketMass / denominator)
    exact (ENNReal.mul_div_cancel hdenominator0 hdenominatorTop).symm
  rw [retainedOwnerPlankFamily_shadingMass]
  change bucketMass ≤ ownerBucketToHRowLoss C q * _
  rw [hbucketIdentity]
  exact mul_le_mul' le_rfl hfloor_le_rowMass

/-- A source-to-retained mass estimate and the honest row selection imply a
division-free mass comparison with the exact bundled row. -/
theorem sourceMass_le_ownerSelectionLoss_mul_hRowMass
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
    (sourceLoss : ENNReal)
    (hsource : D.shading.shadingMass ≤
      sourceLoss * (retainedOwnerPlankFamily D C q).shading.shadingMass) :
    D.shading.shadingMass ≤
      (sourceLoss * ownerBucketToHRowLoss C q) *
        (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive
            B.tau B.S).shading.shadingMass := by
  calc
    D.shading.shadingMass ≤
        sourceLoss * (retainedOwnerPlankFamily D C q).shading.shadingMass :=
      hsource
    _ ≤ sourceLoss * (ownerBucketToHRowLoss C q *
        (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive
            B.tau B.S).shading.shadingMass) := by
      exact mul_le_mul' le_rfl
        (retainedOwnerPlankFamily_mass_le_ownerBucketToHRowLoss_mul_rowMass
          D C q cell hcell selectedCells hmass hactive B)
    _ = (sourceLoss * ownerBucketToHRowLoss C q) *
        (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive
            B.tau B.S).shading.shadingMass := by ring

/-- The mass comparison above upgrades to the required same-row average
comparison because the row shaded union is literally contained in the source
shaded union. -/
theorem sourceAverage_le_ownerSelectionLoss_mul_hRowAverage
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
    (sourceLoss : ENNReal)
    (hsource : D.shading.shadingMass ≤
      sourceLoss * (retainedOwnerPlankFamily D C q).shading.shadingMass) :
    D.shading.averageMultiplicity ≤
      (sourceLoss * ownerBucketToHRowLoss C q) *
        (HRowFreshPlankDatum
          D C q cell hcell selectedCells hmass hactive
            B.tau B.S).shading.averageMultiplicity := by
  let rowD := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  have hmassRow : D.shading.shadingMass ≤
      (sourceLoss * ownerBucketToHRowLoss C q) *
        rowD.shading.shadingMass :=
    sourceMass_le_ownerSelectionLoss_mul_hRowMass
      D C q cell hcell selectedCells hmass hactive B sourceLoss hsource
  have hunion : rowD.shading.shadedUnion ⊆ D.shading.shadedUnion :=
    hRowFreshPlankDatum_shadedUnion_subset_source
      D C q cell hcell selectedCells hmass hactive B.tau B.S
  unfold Shading.averageMultiplicity
  calc
    D.shading.shadingMass / volume D.shading.shadedUnion ≤
        ((sourceLoss * ownerBucketToHRowLoss C q) *
          rowD.shading.shadingMass) / volume D.shading.shadedUnion :=
      ENNReal.div_le_div hmassRow le_rfl
    _ ≤ ((sourceLoss * ownerBucketToHRowLoss C q) *
          rowD.shading.shadingMass) / volume rowD.shading.shadedUnion :=
      ENNReal.div_le_div le_rfl (measure_mono hunion)
    _ = (sourceLoss * ownerBucketToHRowLoss C q) *
        (rowD.shading.shadingMass / volume rowD.shading.shadedUnion) := by
      rw [mul_div_assoc]

#print axioms hRowFreshPlankDatum_shadedUnion_subset_source
#print axioms retainedOwnerPlankFamily_mass_le_ownerBucketToHRowLoss_mul_rowMass
#print axioms sourceMass_le_ownerSelectionLoss_mul_hRowMass
#print axioms sourceAverage_le_ownerSelectionLoss_mul_hRowAverage

end
end Family8HRowSourceAverageRetentionFromOwnerSelectionV1
