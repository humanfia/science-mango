import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThreeShiftCGridWeightedPigeonholeV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedSelectionV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1
open FamilyStickyCinematicL32ThreeShiftCGridWeightedPigeonholeV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u v w z

/-!
# Actual retained pairs on a weight-selected staggered C-grid

This is deliberately parallel to the old cardinal selection.  There is no
claim that one grid label simultaneously retains one third of both an
arbitrary weight and the cardinality.  For compatibility with geometric
consumers, the selected carrier can itself be viewed as an ordinary grid
selection with no further loss.
-/

/-- The actual first C-grid choice with arbitrary `ENNReal` mass retention. -/
structure ActualRetainedY1WeightedThreeShiftCGridSelection
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
    (pairScale : Real) (weight : alpha -> ENNReal) where
  gridLabel : Fin 3
  selected : Finset alpha
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆ items
  grid_weight_retention :
    finiteENNRealWeight items weight ≤
      3 * finiteENNRealWeight selected weight
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

/-- Restrict approximate-pair data to an arbitrary finite subcarrier. -/
theorem ActualRetainedY1ApproxCPairSelection.restrict
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items restricted : Finset alpha}
    {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel}
    {keep : iota -> fineLabel -> Prop} {pairScale cError : Real}
    (S : ActualRetainedY1ApproxCPairSelection D items leftIndex rightIndex
      labelAt keep pairScale cError)
    (hsub : restricted ⊆ items) :
    ActualRetainedY1ApproxCPairSelection D restricted leftIndex rightIndex
      labelAt keep pairScale cError where
  left_retained a ha := S.left_retained a (hsub ha)
  right_retained a ha := S.right_retained a (hsub ha)
  c_gap a ha := S.c_gap a (hsub ha)
  coefficient_lower a ha := S.coefficient_lower a (hsub ha)

/-- The approximate-C selection produces a common weight-maximizing grid. -/
theorem exists_actualRetainedY1WeightedThreeShiftCGridSelection
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
    (hradius : 0 < (radius : Real)) (hitems : items.Nonempty)
    (weight : alpha -> ENNReal) :
    Nonempty (ActualRetainedY1WeightedThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale weight) := by
  let leftC : alpha -> Real := fun a =>
    tubeGraphC (D.fine.tubes (leftIndex a))
  let rightC : alpha -> Real := fun a =>
    tubeGraphC (D.fine.tubes (rightIndex a))
  obtain ⟨W⟩ := exists_weightedThreeShiftCGridSelection
    items leftC rightC hradius hitems (fun a ha => selection.c_gap a ha) weight
  refine ⟨{
    gridLabel := W.gridLabel
    selected := W.selected
    selected_nonempty := W.selected_nonempty
    selected_subset := W.selected_subset
    grid_weight_retention := W.weight_retention
    common_c := ?_
    left_c_change := ?_
    right_c_change := ?_
    coefficient_lower := ?_
    left_retained := ?_
    right_retained := ?_ }⟩
  · intro a ha
    simpa only [threeShiftCGridNormalizeTube,
      tubeGraphC_normalizeTubeC, leftC, rightC] using W.normalized_c_eq a ha
  · intro a ha
    simpa only [threeShiftCGridNormalizeTube,
      tubeGraphC_normalizeTubeC, leftC] using W.left_c_change a ha
  · intro a ha
    simpa only [threeShiftCGridNormalizeTube,
      tubeGraphC_normalizeTubeC, rightC] using W.right_c_change a ha
  · intro a ha
    simpa only [tubePairCoefficientDistance_threeShiftCGridNormalizeTube]
      using selection.coefficient_lower a (W.selected_subset ha)
  · intro a ha
    exact selection.left_retained a (W.selected_subset ha)
  · intro a ha
    exact selection.right_retained a (W.selected_subset ha)

/-- On its already selected carrier, a weighted grid choice supplies the old
geometry-only interface with the identity selection and no further loss. -/
def ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type z} [DecidableEq alpha]
    {D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel}
    {items : Finset alpha} {leftIndex rightIndex : alpha -> iota}
    {labelAt : alpha -> fineLabel} {keep : iota -> fineLabel -> Prop}
    {pairScale : Real} {weight : alpha -> ENNReal}
    (P : ActualRetainedY1WeightedThreeShiftCGridSelection D items
      leftIndex rightIndex labelAt keep pairScale weight) :
    ActualRetainedY1ThreeShiftCGridSelection D P.selected
      leftIndex rightIndex labelAt keep pairScale where
  gridLabel := P.gridLabel
  selected := P.selected
  selected_nonempty := P.selected_nonempty
  selected_subset := Finset.Subset.rfl
  grid_cardinal_retention := by omega
  common_c := P.common_c
  left_c_change := P.left_c_change
  right_c_change := P.right_c_change
  coefficient_lower := P.coefficient_lower
  left_retained := P.left_retained
  right_retained := P.right_retained

#print axioms ActualRetainedY1ApproxCPairSelection.restrict
#print axioms exists_actualRetainedY1WeightedThreeShiftCGridSelection
#print axioms ActualRetainedY1WeightedThreeShiftCGridSelection.toOrdinaryOnSelected

end

end FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridWeightedSelectionV1
