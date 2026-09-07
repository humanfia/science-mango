import Family8Grounding.Family8HRowDisplayedCoefficientCorrelationFromIncidenceV1
import Mathlib.Tactic

/-!
# Same-H-row displayed coefficient incidence from the row mass floor

This file isolates the weakest division-free scalar seam left after the
literal H-row has been selected.  The shaded union of that row lies in the
original unit-scale ambient plank, hence has volume at most one.  The already
proved complete-owner-fibre mass floor then turns the count-weighted floor
budget below into the raw incidence inequality consumed downstream.

The bundle `B` is never reselected, and no canonical/global Frostman constant
is compared or identified.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8HRowDisplayedCoefficientIncidenceFromMassFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8HRowDisplayedCoefficientCorrelationFromIncidenceV1
open Family8PlankHeavyRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankHeavyRetainedOwnerActiveCertifiedOwnerIncidenceV1
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

/-! ## Automatic unit-volume bound for the literal row -/

/-- The shaded union of the exact row stored in `B` lies in the original
unit-scale ambient plank, so its volume is at most one. -/
theorem hRowFreshPlankDatum_volume_shadedUnion_le_one
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
        B.tau B.S).shading.shadedUnion ≤ 1 := by
  let rowD := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  have hunion : rowD.shading.shadedUnion ⊆ (D.ambient : Set Space) := by
    intro x hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    exact D.contained_in_ambient p.2.1
      (rowD.shading.carrier_subset p hp)
  calc
    volume rowD.shading.shadedUnion ≤ volume (D.ambient : Set Space) :=
      measure_mono hunion
    _ ≤ (1 : ENNReal) * 1 := D.ambient_is_unit_scale.volume_upper_bound
    _ = 1 := by simp

/-! ## The weakest remaining division-free scalar budget -/

/-- The displayed coefficient is paid for by the actual number of owners in
the same row times their common half-average mass floor.  This is the weakest
scalar premise needed by the producer below after the automatic unit-volume
bound and the existing row-mass floor are used. -/
def HRowFreshDisplayedCoefficientMassFloorBudget
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
  selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
    correlationLoss *
      (((activeSelectedOwnersInCertifiedSlab
          D C q cell hcell selectedCells hmass hactive
            B.tau B.S).card : ENNReal) *
        retainedOwnerHalfAverageFloor C q)

/-- The count-weighted row mass-floor budget produces the precise
division-free same-`B` incidence inequality. -/
theorem hRowFreshDisplayedCoefficientRowIncidence_of_massFloorBudget
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
    (hBudget : HRowFreshDisplayedCoefficientMassFloorBudget
      (delta := delta) X selectorLoss outputEta
      D C q cell hcell selectedCells hmass hactive B correlationLoss) :
    HRowFreshDisplayedCoefficientRowIncidence
      (delta := delta) X selectorLoss outputEta
      D C q cell hcell selectedCells hmass hactive B correlationLoss := by
  let rowD := HRowFreshPlankDatum
    D C q cell hcell selectedCells hmass hactive B.tau B.S
  let rowFloor : ENNReal :=
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selectedCells hmass hactive
          B.tau B.S).card : ENNReal) *
      retainedOwnerHalfAverageFloor C q
  have hvolume : volume rowD.shading.shadedUnion ≤ 1 :=
    hRowFreshPlankDatum_volume_shadedUnion_le_one
      D C q cell hcell selectedCells hmass hactive B
  have hfloor : rowFloor ≤ rowD.shading.shadingMass := by
    simpa only [rowFloor, rowD] using
      activeSelectedOwnerRow_card_mul_floor_le_shadingMass
        D C q cell hcell selectedCells hmass hactive B.tau B.S
  change
    (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
        volume rowD.shading.shadedUnion ≤
      correlationLoss * rowD.shading.shadingMass
  calc
    (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
          volume rowD.shading.shadedUnion ≤
        (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) * 1 :=
      mul_le_mul' le_rfl hvolume
    _ = selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) := by
      simp
    _ ≤ correlationLoss * rowFloor := by
      exact hBudget
    _ ≤ correlationLoss * rowD.shading.shadingMass :=
      mul_le_mul' le_rfl hfloor

/-- Direct downstream endpoint: the same budget yields the row-average
correlation in the only direction consumed by the automatic Prop. 6.6
connector. -/
theorem hRowFreshDisplayedCoefficientRowCorrelation_of_massFloorBudget
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
    (hBudget : HRowFreshDisplayedCoefficientMassFloorBudget
      (delta := delta) X selectorLoss outputEta
      D C q cell hcell selectedCells hmass hactive B correlationLoss) :
    HRowFreshDisplayedCoefficientRowCorrelation
      (delta := delta) X selectorLoss outputEta
      D C q cell hcell selectedCells hmass hactive B correlationLoss := by
  apply hRowFreshDisplayedCoefficientRowCorrelation_of_incidence
    (delta := delta) X selectorLoss outputEta
    D C q cell hcell selectedCells hmass hactive B correlationLoss
  exact hRowFreshDisplayedCoefficientRowIncidence_of_massFloorBudget
    (delta := delta) X selectorLoss outputEta
    D C q cell hcell selectedCells hmass hactive B correlationLoss hBudget

#print axioms hRowFreshPlankDatum_volume_shadedUnion_le_one
#print axioms hRowFreshDisplayedCoefficientRowIncidence_of_massFloorBudget
#print axioms hRowFreshDisplayedCoefficientRowCorrelation_of_massFloorBudget

end
end Family8HRowDisplayedCoefficientIncidenceFromMassFloorV1
