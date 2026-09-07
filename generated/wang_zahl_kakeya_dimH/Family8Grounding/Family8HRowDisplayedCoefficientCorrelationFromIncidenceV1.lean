import Family8Grounding.Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Mathlib.Tactic

/-!
# Same-row displayed-coefficient correlation from raw incidence

The downstream automatic factor sandwich asks for the displayed coefficient
to be bounded by a correlation loss times the average multiplicity of the
literal H-row.  The incidence-counting form of that statement has no
division: coefficient times the same row's shaded-union volume is bounded by
correlation loss times the same row's shading mass.

This file performs only that ratio conversion.  Nonzero row mass, nonzero
shaded-union volume, and finite shaded-union volume are proved for the exact
row already stored in the supplied `HRowFreshPropertyBundle`; no row or fresh
subtype is reselected.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowDisplayedCoefficientCorrelationFromIncidenceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyTubeDatumV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe v

variable {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
variable {a b : NNReal}

/-! ## Positivity of the exact bundled H-row -/

/-- The complete-owner-fibre row in an H-row fresh bundle has nonzero mass.
The proof uses the same certified row and the positive half-average of the
nonzero retained owner bucket. -/
theorem hRowFreshPlankDatum_shadingMass_ne_zero
    (D : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow) :
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive
        B.tau B.S).shading.shadingMass ≠ 0 := by
  have hbucketMass0 :
      (∑ s ∈ selectedOwnerLogBucket C q, ownerFiberMass C s) ≠ 0 := by
    intro hzero
    apply hmass
    rw [retainedOwnerPlankFamily_shadingMass]
    exact hzero
  have hfloor0 : retainedOwnerHalfAverageFloor C q ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    exact ⟨hbucketMass0, ENNReal.mul_ne_top
      (by norm_num) (ENNReal.natCast_ne_top _)⟩
  have hcardNat0 :
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive
          B.tau B.S).card ≠ 0 :=
    Finset.card_ne_zero.mpr B.hrow
  have hcard0 :
      ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive
          B.tau B.S).card : ENNReal) ≠ 0 := by
    exact_mod_cast hcardNat0
  have hproduct0 :
      ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive
          B.tau B.S).card : ENNReal) *
          retainedOwnerHalfAverageFloor C q ≠ 0 :=
    mul_ne_zero hcard0 hfloor0
  have hrowFloor :=
    activeSelectedOwnerRow_card_mul_floor_le_shadingMass
      D C q cell hcell selectedCells hmass hactive B.tau B.S
  intro hrowMass0
  apply hproduct0
  apply le_antisymm
  · simpa only [hrowMass0] using hrowFloor
  · exact bot_le

/-- Consequently the exact bundled H-row has nonzero shaded-union volume. -/
theorem hRowFreshPlankDatum_volume_shadedUnion_ne_zero
    (D : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow) :
    volume (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive
        B.tau B.S).shading.shadedUnion ≠ 0 := by
  exact volume_shadedUnion_ne_zero_of_shadingMass_ne_zero
    (HRowFreshPlankDatum
      D C q cell hcell selectedCells hmass hactive B.tau B.S).shading
    (hRowFreshPlankDatum_shadingMass_ne_zero
      D C q cell hcell selectedCells hmass hactive B)

/-! ## Division-free incidence seam -/

/-- The raw incidence-counting form of the displayed coefficient bound.
Every term is attached to the literal row selected by the same bundle `B`.
-/
def HRowFreshDisplayedCoefficientRowIncidence
    {delta : NNReal}
    (X selectorLoss : ENNReal) (outputEta : Real)
    (D : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (correlationLoss : ENNReal) : Prop :=
  (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
      volume (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive
          B.tau B.S).shading.shadedUnion ≤
    correlationLoss *
      (HRowFreshPlankDatum
        D C q cell hcell selectedCells hmass hactive
          B.tau B.S).shading.shadingMass

/-- Division by the exact same row volume converts raw incidence counting
into the existing downstream row-correlation obligation. -/
theorem hRowFreshDisplayedCoefficientRowCorrelation_of_incidence
    {delta : NNReal}
    (X selectorLoss : ENNReal) (outputEta : Real)
    (D : ShadedConvexPlankFamily rowIndex a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card rowIndex) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selectedCells : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices
      D C q cell hcell selectedCells).Nonempty)
    {epsilonRow betaRow etaRow : Real}
    (B : HRowFreshPropertyBundle
      D C q cell hcell selectedCells hmass hactive
        epsilonRow betaRow etaRow)
    (correlationLoss : ENNReal)
    (hIncidence : HRowFreshDisplayedCoefficientRowIncidence
      (delta := delta) X selectorLoss outputEta
      D C q cell hcell selectedCells hmass hactive B correlationLoss) :
    HRowFreshDisplayedCoefficientRowCorrelation
      (delta := delta) X selectorLoss outputEta
      D C q cell hcell selectedCells hmass hactive B correlationLoss := by
  let rowD := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  have hvolume0 : volume rowD.shading.shadedUnion ≠ 0 :=
    hRowFreshPlankDatum_volume_shadedUnion_ne_zero
      D C q cell hcell selectedCells hmass hactive B
  have hvolumeTop : volume rowD.shading.shadedUnion ≠ ∞ :=
    volume_shadedUnion_ne_top rowD.shading
  change selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
    correlationLoss *
      (rowD.shading.shadingMass / volume rowD.shading.shadedUnion)
  rw [← mul_div_assoc]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hvolume0) (Or.inl hvolumeTop)).2
  change
    (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
        volume rowD.shading.shadedUnion ≤
      correlationLoss * rowD.shading.shadingMass
  exact hIncidence

#print axioms hRowFreshPlankDatum_shadingMass_ne_zero
#print axioms hRowFreshPlankDatum_volume_shadedUnion_ne_zero
#print axioms hRowFreshDisplayedCoefficientRowCorrelation_of_incidence

end
end Family8HRowDisplayedCoefficientCorrelationFromIncidenceV1
