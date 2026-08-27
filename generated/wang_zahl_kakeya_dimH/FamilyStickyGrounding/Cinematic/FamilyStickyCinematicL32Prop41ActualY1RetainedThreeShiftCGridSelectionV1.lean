import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1
open FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v w z

/-!
# Actual retained pairs on one uniform staggered graph-C grid

For a fixed grid label, every tube is transformed as a function of that tube
alone.  In particular, the same original tube cannot split into several
normalised tubes merely because it occurs in several retained pairs.
-/

/-- A lossless description of the first, C-grid, `Fin 3` selection stage. -/
structure ActualRetainedY1ThreeShiftCGridSelection
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (items : Finset alpha)
    (leftIndex rightIndex : alpha -> iota)
    (labelAt : alpha -> fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (pairScale : Real) where
  gridLabel : Fin 3
  selected : Finset alpha
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆ items
  grid_cardinal_retention : items.card ≤ 3 * selected.card
  common_c : forall a, a ∈ selected ->
    tubeGraphC
        (threeShiftCGridNormalizeTube gridLabel
          (D.fine.tubes (leftIndex a))) =
      tubeGraphC
        (threeShiftCGridNormalizeTube gridLabel
          (D.fine.tubes (rightIndex a)))
  left_c_change : forall a, a ∈ selected ->
    |tubeGraphC (D.fine.tubes (leftIndex a)) -
        tubeGraphC
          (threeShiftCGridNormalizeTube gridLabel
            (D.fine.tubes (leftIndex a)))| ≤ (radius : Real)
  right_c_change : forall a, a ∈ selected ->
    |tubeGraphC (D.fine.tubes (rightIndex a)) -
        tubeGraphC
          (threeShiftCGridNormalizeTube gridLabel
            (D.fine.tubes (rightIndex a)))| ≤ (radius : Real)
  coefficient_lower : forall a, a ∈ selected ->
    2 * pairScale ≤ tubePairCoefficientDistance
      (threeShiftCGridNormalizeTube gridLabel
        (D.fine.tubes (leftIndex a)))
      (threeShiftCGridNormalizeTube gridLabel
        (D.fine.tubes (rightIndex a)))
  left_retained : forall a, a ∈ selected ->
    (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep
  right_retained : forall a, a ∈ selected ->
    (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep

/-- The approximate-C selection canonically produces a uniform grid label on
at least one third of the input pairs. -/
theorem exists_actualRetainedY1ThreeShiftCGridSelection
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (items : Finset alpha)
    (leftIndex rightIndex : alpha -> iota)
    (labelAt : alpha -> fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (pairScale : Real)
    (selection : ActualRetainedY1ApproxCPairSelection D items
      leftIndex rightIndex labelAt keep pairScale (radius : Real))
    (hradius : 0 < (radius : Real)) (hitems : items.Nonempty) :
    Nonempty (ActualRetainedY1ThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale) := by
  let leftC : alpha -> Real := fun a =>
    tubeGraphC (D.fine.tubes (leftIndex a))
  let rightC : alpha -> Real := fun a =>
    tubeGraphC (D.fine.tubes (rightIndex a))
  obtain ⟨k, fiber, hfiber, hsubset, hcard, hgood, hcenter,
      hleftChange, hrightChange⟩ :=
    exists_uniform_threeShiftCGrid_fiber items leftC rightC hradius hitems
      (fun a ha => selection.c_gap a ha)
  refine ⟨{
    gridLabel := k
    selected := fiber
    selected_nonempty := hfiber
    selected_subset := hsubset
    grid_cardinal_retention := hcard
    common_c := ?_
    left_c_change := ?_
    right_c_change := ?_
    coefficient_lower := ?_
    left_retained := ?_
    right_retained := ?_ }⟩
  · intro a ha
    simpa only [threeShiftCGridNormalizeTube,
      tubeGraphC_normalizeTubeC, leftC, rightC] using hcenter a ha
  · intro a ha
    simpa only [threeShiftCGridNormalizeTube,
      tubeGraphC_normalizeTubeC, leftC] using hleftChange a ha
  · intro a ha
    simpa only [threeShiftCGridNormalizeTube,
      tubeGraphC_normalizeTubeC, rightC] using hrightChange a ha
  · intro a ha
    simpa only [
      tubePairCoefficientDistance_threeShiftCGridNormalizeTube]
      using selection.coefficient_lower a (hsubset ha)
  · intro a ha
    exact selection.left_retained a (hsubset ha)
  · intro a ha
    exact selection.right_retained a (hsubset ha)

/-- For fixed `gridLabel`, the selected left transformed tubes factor through
the selected left index carrier.  Hence pair repetition causes no card loss. -/
theorem selected_left_gridTube_image_card_le_index_image
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
    (P.selected.image fun a =>
      threeShiftCGridNormalizeTube P.gridLabel
        (D.fine.tubes (leftIndex a))).card ≤
      (P.selected.image leftIndex).card := by
  classical
  let transform : iota -> Tube radius := fun i =>
    threeShiftCGridNormalizeTube P.gridLabel (D.fine.tubes i)
  change (P.selected.image (transform ∘ leftIndex)).card ≤
    (P.selected.image leftIndex).card
  rw [← Finset.image_image]
  exact Finset.card_image_le

/-- The identical factorisation bound for right transformed tubes. -/
theorem selected_right_gridTube_image_card_le_index_image
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
    (P.selected.image fun a =>
      threeShiftCGridNormalizeTube P.gridLabel
        (D.fine.tubes (rightIndex a))).card ≤
      (P.selected.image rightIndex).card := by
  classical
  let transform : iota -> Tube radius := fun i =>
    threeShiftCGridNormalizeTube P.gridLabel (D.fine.tubes i)
  change (P.selected.image (transform ∘ rightIndex)).card ≤
    (P.selected.image rightIndex).card
  rw [← Finset.image_image]
  exact Finset.card_image_le

#print axioms abs_tubeGraphC_threeShiftCGridNormalizeTube_sub_le
#print axioms exists_actualRetainedY1ThreeShiftCGridSelection

end

end FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
