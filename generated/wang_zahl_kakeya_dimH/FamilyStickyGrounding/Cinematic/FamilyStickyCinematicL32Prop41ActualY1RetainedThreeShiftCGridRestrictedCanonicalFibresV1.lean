import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ActualTubeConstantShiftV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridCanonicalFibresV1

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32FiniteValueFibresV1
open FamilyStickyCinematicL32FiniteValuePairCarrierV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridCanonicalFibresV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v w z

/-!
# Restricted canonical fibres after the global trace shift

The second `Fin 3` pigeonhole stage returns a survivor family contained in
the first-stage grid selection.  Its left endpoint has also received one
globally fixed trace translation.  This module partitions precisely those
final endpoints, rather than the larger first-stage carrier.
-/

section Restricted

variable {point : Type u} [MeasurableSpace point]
variable {radius : NNReal} {iota : Type v} [DecidableEq iota]
variable {fineLabel : Type w} [DecidableEq fineLabel]
variable {alpha : Type z} [DecidableEq alpha]
variable {D : CoarseRectangleIncidenceData
  (point := point) (radius := radius) (iota := iota) fineLabel}
variable {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
variable {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
variable {pairScale : Real}
variable (P : ActualRetainedY1ThreeShiftCGridSelection D items
  leftIndex rightIndex labelAt keep pairScale)

/-- Final left endpoint: fixed grid normalisation followed by one globally
fixed trace translation. -/
def actualThreeShiftCGridRestrictedTraceLeftTube
    (shift : Real) (a : alpha) : Tube radius :=
  traceTranslateTube (actualThreeShiftCGridLeftTube P a) shift

/-- Final right endpoint; the trace theorem leaves this side untranslated. -/
def actualThreeShiftCGridRestrictedRightTube (a : alpha) : Tube radius :=
  actualThreeShiftCGridRightTube P a

/-- Canonical value read from the actual final left endpoint. -/
def actualThreeShiftCGridRestrictedValueAt
    (shift : Real) (a : alpha) : Real :=
  tubeGraphC (actualThreeShiftCGridRestrictedTraceLeftTube P shift a)

@[simp] theorem actualThreeShiftCGridRestrictedValueAt_eq_base
    (shift : Real) (a : alpha) :
    actualThreeShiftCGridRestrictedValueAt P shift a =
      actualThreeShiftCGridValueAt P a := by
  simp [actualThreeShiftCGridRestrictedValueAt,
    actualThreeShiftCGridRestrictedTraceLeftTube,
    actualThreeShiftCGridValueAt]

theorem actualThreeShiftCGridRestrictedRightTube_graphC_eq_valueAt
    {survivors : Finset alpha} (hsub : survivors ⊆ P.selected)
    (shift : Real) {a : alpha} (ha : a ∈ survivors) :
    tubeGraphC (actualThreeShiftCGridRestrictedRightTube P a) =
      actualThreeShiftCGridRestrictedValueAt P shift a := by
  rw [actualThreeShiftCGridRestrictedValueAt_eq_base]
  exact (P.common_c a (hsub ha)).symm

noncomputable def actualThreeShiftCGridRestrictedOccupiedValues
    (survivors : Finset alpha) (shift : Real) : Finset Real :=
  finiteOccupiedValues survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)

/-- Raw final-survivor fibre at one exact normalised C value. -/
noncomputable def actualThreeShiftCGridRestrictedFiber
    (survivors : Finset alpha) (shift c : Real) : Finset alpha :=
  finiteValueFiber survivors
    (actualThreeShiftCGridRestrictedValueAt P shift) c

noncomputable def actualThreeShiftCGridRestrictedTubeFamilyAt
    (survivors : Finset alpha) (shift c : Real) : Finset (Tube radius) :=
  finiteValuePairCarrierAt survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)
    (actualThreeShiftCGridRestrictedTraceLeftTube P shift)
    (actualThreeShiftCGridRestrictedRightTube P) c

noncomputable def actualThreeShiftCGridRestrictedGlobalTubeFamily
    (survivors : Finset alpha) (shift : Real) : Finset (Tube radius) :=
  finitePairCarrier survivors
    (actualThreeShiftCGridRestrictedTraceLeftTube P shift)
    (actualThreeShiftCGridRestrictedRightTube P)

theorem actualThreeShiftCGridRestrictedFiber_nonempty
    {survivors : Finset alpha} {shift c : Real}
    (hc : c ∈ actualThreeShiftCGridRestrictedOccupiedValues P survivors shift) :
    (actualThreeShiftCGridRestrictedFiber P survivors shift c).Nonempty := by
  exact finiteValueFiber_nonempty_of_mem survivors
    (actualThreeShiftCGridRestrictedValueAt P shift) hc

theorem actualThreeShiftCGridRestrictedFiber_subset
    (survivors : Finset alpha) (shift c : Real) :
    actualThreeShiftCGridRestrictedFiber P survivors shift c ⊆ survivors := by
  exact finiteValueFiber_subset survivors
    (actualThreeShiftCGridRestrictedValueAt P shift) c

theorem actualThreeShiftCGridRestrictedFiber_common_c
    {survivors : Finset alpha} (hsub : survivors ⊆ P.selected)
    (shift c : Real) :
    forall a, a ∈ actualThreeShiftCGridRestrictedFiber P survivors shift c ->
      tubeGraphC
          (actualThreeShiftCGridRestrictedTraceLeftTube P shift a) = c ∧
        tubeGraphC
          (actualThreeShiftCGridRestrictedRightTube P a) = c := by
  intro a ha
  have haData := (mem_finiteValueFiber_iff survivors
    (actualThreeShiftCGridRestrictedValueAt P shift) c a).mp ha
  have hright := actualThreeShiftCGridRestrictedRightTube_graphC_eq_valueAt
    P hsub shift haData.1
  exact ⟨haData.2, hright.trans haData.2⟩

theorem actualThreeShiftCGridRestricted_survivors_card_eq_sum_fiber_card
    (survivors : Finset alpha) (shift : Real) :
    survivors.card =
      ∑ c ∈ actualThreeShiftCGridRestrictedOccupiedValues P survivors shift,
        (actualThreeShiftCGridRestrictedFiber P survivors shift c).card := by
  exact card_eq_sum_finiteValueFiber_card survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)

theorem pairwiseDisjoint_actualThreeShiftCGridRestrictedFiber
    (survivors : Finset alpha) (shift : Real) :
    Set.PairwiseDisjoint
      (actualThreeShiftCGridRestrictedOccupiedValues P survivors shift :
        Set Real)
      (actualThreeShiftCGridRestrictedFiber P survivors shift) := by
  exact pairwiseDisjoint_finiteValueFiber survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)

theorem biUnion_actualThreeShiftCGridRestrictedFiber_eq_survivors
    (survivors : Finset alpha) (shift : Real) :
    (actualThreeShiftCGridRestrictedOccupiedValues P survivors shift).biUnion
        (actualThreeShiftCGridRestrictedFiber P survivors shift) =
      survivors := by
  exact biUnion_finiteValueFiber_eq survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)

theorem pairwiseDisjoint_actualThreeShiftCGridRestrictedTubeFamilyAt
    {survivors : Finset alpha} (hsub : survivors ⊆ P.selected)
    (shift : Real) :
    Set.PairwiseDisjoint
      (actualThreeShiftCGridRestrictedOccupiedValues P survivors shift :
        Set Real)
      (actualThreeShiftCGridRestrictedTubeFamilyAt P survivors shift) := by
  apply pairwiseDisjoint_finiteValuePairCarrierAt survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)
    (actualThreeShiftCGridRestrictedTraceLeftTube P shift)
    (actualThreeShiftCGridRestrictedRightTube P) tubeGraphC
  · intro _a _ha
    rfl
  · intro a ha
    exact actualThreeShiftCGridRestrictedRightTube_graphC_eq_valueAt
      P hsub shift ha

theorem biUnion_actualThreeShiftCGridRestrictedTubeFamilyAt_eq_global
    (survivors : Finset alpha) (shift : Real) :
    (actualThreeShiftCGridRestrictedOccupiedValues P survivors shift).biUnion
        (actualThreeShiftCGridRestrictedTubeFamilyAt P survivors shift) =
      actualThreeShiftCGridRestrictedGlobalTubeFamily P survivors shift := by
  exact biUnion_finiteValuePairCarrierAt_eq_global survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)
    (actualThreeShiftCGridRestrictedTraceLeftTube P shift)
    (actualThreeShiftCGridRestrictedRightTube P)

theorem actualThreeShiftCGridRestrictedGlobalTubeFamily_card_eq_sum_fiber_card
    {survivors : Finset alpha} (hsub : survivors ⊆ P.selected)
    (shift : Real) :
    (actualThreeShiftCGridRestrictedGlobalTubeFamily P survivors shift).card =
      ∑ c ∈ actualThreeShiftCGridRestrictedOccupiedValues P survivors shift,
        (actualThreeShiftCGridRestrictedTubeFamilyAt P survivors shift c).card := by
  apply finitePairCarrier_card_eq_sum_valueFiber_card survivors
    (actualThreeShiftCGridRestrictedValueAt P shift)
    (actualThreeShiftCGridRestrictedTraceLeftTube P shift)
    (actualThreeShiftCGridRestrictedRightTube P) tubeGraphC
  · intro _a _ha
    rfl
  · intro a ha
    exact actualThreeShiftCGridRestrictedRightTube_graphC_eq_valueAt
      P hsub shift ha

/-- The global trace-shifted left endpoints still factor through the original
left index carrier, because both the grid label and trace shift are fixed. -/
theorem actualThreeShiftCGridRestrictedTraceLeft_image_card_le_index_image
    (survivors : Finset alpha) (shift : Real) :
    (survivors.image
      (actualThreeShiftCGridRestrictedTraceLeftTube P shift)).card ≤
      (survivors.image leftIndex).card := by
  let transform : iota -> Tube radius := fun i =>
    traceTranslateTube
      (threeShiftCGridNormalizeTube P.gridLabel (D.fine.tubes i)) shift
  change (survivors.image (transform ∘ leftIndex)).card ≤
    (survivors.image leftIndex).card
  rw [← Finset.image_image]
  exact Finset.card_image_le

theorem actualThreeShiftCGridRestrictedRight_image_card_le_index_image
    (survivors : Finset alpha) :
    (survivors.image
      (actualThreeShiftCGridRestrictedRightTube P)).card ≤
      (survivors.image rightIndex).card := by
  let transform : iota -> Tube radius := fun i =>
    threeShiftCGridNormalizeTube P.gridLabel (D.fine.tubes i)
  change (survivors.image (transform ∘ rightIndex)).card ≤
    (survivors.image rightIndex).card
  rw [← Finset.image_image]
  exact Finset.card_image_le

/-- Honest load bridge on the exact final trace fibre. -/
theorem actualThreeShiftCGridRestrictedGlobalTubeFamily_card_le_index_images
    (survivors : Finset alpha) (shift : Real) :
    (actualThreeShiftCGridRestrictedGlobalTubeFamily P survivors shift).card ≤
      (survivors.image leftIndex).card +
        (survivors.image rightIndex).card := by
  calc
    (actualThreeShiftCGridRestrictedGlobalTubeFamily P survivors shift).card ≤
        (survivors.image
          (actualThreeShiftCGridRestrictedTraceLeftTube P shift)).card +
          (survivors.image
            (actualThreeShiftCGridRestrictedRightTube P)).card := by
      exact Finset.card_union_le _ _
    _ ≤ (survivors.image leftIndex).card +
        (survivors.image rightIndex).card :=
      Nat.add_le_add
        (actualThreeShiftCGridRestrictedTraceLeft_image_card_le_index_image
          P survivors shift)
        (actualThreeShiftCGridRestrictedRight_image_card_le_index_image
          P survivors)

end Restricted

#print axioms actualThreeShiftCGridRestrictedFiber_common_c
#print axioms actualThreeShiftCGridRestricted_survivors_card_eq_sum_fiber_card
#print axioms pairwiseDisjoint_actualThreeShiftCGridRestrictedTubeFamilyAt
#print axioms biUnion_actualThreeShiftCGridRestrictedTubeFamilyAt_eq_global
#print axioms actualThreeShiftCGridRestrictedGlobalTubeFamily_card_le_index_images

end


end FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
