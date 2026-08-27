import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteValuePairCarrierV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridCanonicalFibresV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32FiniteValueFibresV1
open FamilyStickyCinematicL32FiniteValuePairCarrierV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v w z

/-!
# Canonical common-C fibres after fixed-grid normalisation

The grid label has already been made uniform.  Consequently both endpoint
maps below are fixed functions of the original endpoint tube.  Partitioning
by the normalised left graph-C is lossless on selected pairs; literal common C
makes the corresponding deduplicated endpoint carriers disjoint as well.
-/

def actualThreeShiftCGridLeftTube
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) (a : alpha) : Tube radius :=
  threeShiftCGridNormalizeTube P.gridLabel (D.fine.tubes (leftIndex a))

def actualThreeShiftCGridRightTube
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) (a : alpha) : Tube radius :=
  threeShiftCGridNormalizeTube P.gridLabel (D.fine.tubes (rightIndex a))

/-- Canonical fibre value.  On selected pairs this is also the right endpoint
graph-C, by `P.common_c`. -/
def actualThreeShiftCGridValueAt
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) (a : alpha) : Real :=
  tubeGraphC (actualThreeShiftCGridLeftTube P a)

noncomputable def actualThreeShiftCGridOccupiedValues
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) : Finset Real :=
  finiteOccupiedValues P.selected (actualThreeShiftCGridValueAt P)

noncomputable def actualThreeShiftCGridFiber
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) (c : Real) : Finset alpha :=
  finiteValueFiber P.selected (actualThreeShiftCGridValueAt P) c

noncomputable def actualThreeShiftCGridTubeFamilyAt
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) (c : Real) :
    Finset (Tube radius) :=
  finiteValuePairCarrierAt P.selected (actualThreeShiftCGridValueAt P)
    (actualThreeShiftCGridLeftTube P) (actualThreeShiftCGridRightTube P) c

noncomputable def actualThreeShiftCGridGlobalTubeFamily
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) : Finset (Tube radius) :=
  finitePairCarrier P.selected (actualThreeShiftCGridLeftTube P)
    (actualThreeShiftCGridRightTube P)

theorem actualThreeShiftCGridFiber_nonempty
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) {c : Real}
    (hc : c ∈ actualThreeShiftCGridOccupiedValues P) :
    (actualThreeShiftCGridFiber P c).Nonempty := by
  exact finiteValueFiber_nonempty_of_mem P.selected
    (actualThreeShiftCGridValueAt P) hc

theorem actualThreeShiftCGridFiber_subset
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) (c : Real) :
    actualThreeShiftCGridFiber P c ⊆ P.selected := by
  exact finiteValueFiber_subset P.selected
    (actualThreeShiftCGridValueAt P) c

theorem actualThreeShiftCGridFiber_common_c
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) (c : Real) :
    forall a, a ∈ actualThreeShiftCGridFiber P c ->
      tubeGraphC (actualThreeShiftCGridLeftTube P a) = c ∧
        tubeGraphC (actualThreeShiftCGridRightTube P a) = c := by
  intro a ha
  have haData := (mem_finiteValueFiber_iff P.selected
    (actualThreeShiftCGridValueAt P) c a).mp ha
  have hcommon := P.common_c a haData.1
  exact ⟨haData.2, hcommon.symm.trans haData.2⟩

theorem actualThreeShiftCGrid_selected_card_eq_sum_fiber_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) :
    P.selected.card =
      ∑ c ∈ actualThreeShiftCGridOccupiedValues P,
        (actualThreeShiftCGridFiber P c).card := by
  exact card_eq_sum_finiteValueFiber_card P.selected
    (actualThreeShiftCGridValueAt P)

theorem pairwiseDisjoint_actualThreeShiftCGridTubeFamilyAt
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) :
    Set.PairwiseDisjoint (actualThreeShiftCGridOccupiedValues P : Set Real)
      (actualThreeShiftCGridTubeFamilyAt P) := by
  apply pairwiseDisjoint_finiteValuePairCarrierAt P.selected
    (actualThreeShiftCGridValueAt P)
    (actualThreeShiftCGridLeftTube P) (actualThreeShiftCGridRightTube P)
    tubeGraphC
  · intro _a _ha
    rfl
  · intro a ha
    exact (P.common_c a ha).symm

theorem biUnion_actualThreeShiftCGridTubeFamilyAt_eq_global
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) :
    (actualThreeShiftCGridOccupiedValues P).biUnion
        (actualThreeShiftCGridTubeFamilyAt P) =
      actualThreeShiftCGridGlobalTubeFamily P := by
  exact biUnion_finiteValuePairCarrierAt_eq_global P.selected
    (actualThreeShiftCGridValueAt P)
    (actualThreeShiftCGridLeftTube P) (actualThreeShiftCGridRightTube P)

theorem actualThreeShiftCGridGlobalTubeFamily_card_eq_sum_fiber_card
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) :
    (actualThreeShiftCGridGlobalTubeFamily P).card =
      ∑ c ∈ actualThreeShiftCGridOccupiedValues P,
        (actualThreeShiftCGridTubeFamilyAt P c).card := by
  apply finitePairCarrier_card_eq_sum_valueFiber_card P.selected
    (actualThreeShiftCGridValueAt P)
    (actualThreeShiftCGridLeftTube P) (actualThreeShiftCGridRightTube P)
    tubeGraphC
  · intro _a _ha
    rfl
  · intro a ha
    exact (P.common_c a ha).symm

/-- Honest no-multiplicity bound: the global normalised endpoint family is
controlled by the two separate original endpoint index images. -/
theorem actualThreeShiftCGridGlobalTubeFamily_card_le_index_images
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real}
    (P : ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) :
    (actualThreeShiftCGridGlobalTubeFamily P).card ≤
      (P.selected.image leftIndex).card +
        (P.selected.image rightIndex).card := by
  classical
  calc
    (actualThreeShiftCGridGlobalTubeFamily P).card ≤
        (P.selected.image (actualThreeShiftCGridLeftTube P)).card +
          (P.selected.image (actualThreeShiftCGridRightTube P)).card := by
      exact Finset.card_union_le _ _
    _ ≤ (P.selected.image leftIndex).card +
        (P.selected.image rightIndex).card :=
      Nat.add_le_add
        (selected_left_gridTube_image_card_le_index_image P)
        (selected_right_gridTube_image_card_le_index_image P)

#print axioms actualThreeShiftCGridFiber_common_c
#print axioms actualThreeShiftCGrid_selected_card_eq_sum_fiber_card
#print axioms pairwiseDisjoint_actualThreeShiftCGridTubeFamilyAt
#print axioms biUnion_actualThreeShiftCGridTubeFamilyAt_eq_global
#print axioms actualThreeShiftCGridGlobalTubeFamily_card_le_index_images

end

end FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridCanonicalFibresV1
