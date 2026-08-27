import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32ThreeShiftCGridWeightedPigeonholeV1

open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
open FamilyStickyCinematicL32Prop41WeightedThreeShiftPigeonholeV1
open FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1

noncomputable section

universe u

/-!
# Weighted staggered C-grid selection

The two endpoint C-values still choose a valid staggered grid pointwise, but
the common grid is now selected by arbitrary `ENNReal` mass rather than by
cardinality.  The resulting normalized endpoints remain functions of their
own source endpoints; only the finite choice criterion changes.
-/

/-- Data returned by one weight-aware common C-grid selection. -/
structure WeightedThreeShiftCGridSelection
    {alpha : Type u} [DecidableEq alpha]
    (items : Finset alpha) (leftC rightC : alpha -> Real)
    (r : Real) (weight : alpha -> ENNReal) where
  gridLabel : Fin 3
  selected : Finset alpha
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆ items
  weight_retention :
    finiteENNRealWeight items weight ≤
      3 * finiteENNRealWeight selected weight
  grid_good : forall a, a ∈ selected ->
    GoodThreeShiftCGridPair r (leftC a) (rightC a) gridLabel
  normalized_c_eq : forall a, a ∈ selected ->
    threeShiftNormalizedC r gridLabel (leftC a) =
      threeShiftNormalizedC r gridLabel (rightC a)
  left_c_change : forall a, a ∈ selected ->
    |leftC a - threeShiftNormalizedC r gridLabel (leftC a)| ≤ r
  right_c_change : forall a, a ∈ selected ->
    |rightC a - threeShiftNormalizedC r gridLabel (rightC a)| ≤ r

/-- Pointwise C-gap control produces a common grid retaining at least one
third of any prescribed `ENNReal` weight. -/
theorem exists_weightedThreeShiftCGridSelection
    {alpha : Type u} [DecidableEq alpha]
    (items : Finset alpha) (leftC rightC : alpha -> Real)
    {r : Real} (hr : 0 < r) (hitems : items.Nonempty)
    (hgap : forall a, a ∈ items -> |leftC a - rightC a| ≤ r)
    (weight : alpha -> ENNReal) :
    Nonempty (WeightedThreeShiftCGridSelection
      items leftC rightC r weight) := by
  let good : alpha -> Fin 3 -> Prop := fun a k =>
    GoodThreeShiftCGridPair r (leftC a) (rightC a) k
  have hgood : forall a, a ∈ items -> ∃ k : Fin 3, good a k := by
    intro a ha
    exact exists_goodThreeShiftCGridPair hr (hgap a ha)
  obtain ⟨k, hfiber, hsubset, hweight, hfiberGood⟩ :=
    exists_uniform_threeShift_weighted_fiber items good weight hitems hgood
  let fiber := threeShiftFiber items
    (chosenThreeShiftLabel items good hgood) k
  refine ⟨{
    gridLabel := k
    selected := fiber
    selected_nonempty := ?_
    selected_subset := ?_
    weight_retention := ?_
    grid_good := ?_
    normalized_c_eq := ?_
    left_c_change := ?_
    right_c_change := ?_ }⟩
  · simpa only [fiber] using hfiber
  · simpa only [fiber] using hsubset
  · simpa only [fiber] using hweight
  · intro a ha
    have ha' : a ∈ threeShiftFiber items
        (chosenThreeShiftLabel items good hgood) k := by
      simpa only [fiber] using ha
    exact hfiberGood a ha'
  · intro a ha
    exact goodThreeShiftCGridPair_normalized_eq
      ((show good a k by
        have ha' : a ∈ threeShiftFiber items
            (chosenThreeShiftLabel items good hgood) k := by
          simpa only [fiber] using ha
        exact hfiberGood a ha'))
  · intro _a _ha
    exact abs_sub_threeShiftNormalizedC_le hr k
  · intro _a _ha
    exact abs_sub_threeShiftNormalizedC_le hr k

#print axioms exists_weightedThreeShiftCGridSelection

end

end FamilyStickyCinematicL32ThreeShiftCGridWeightedPigeonholeV1
