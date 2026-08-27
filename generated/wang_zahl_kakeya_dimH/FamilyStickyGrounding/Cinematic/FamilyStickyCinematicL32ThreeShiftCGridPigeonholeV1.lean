import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThreeShiftCGridV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1

open FamilyStickyCinematicL32ThreeShiftCGridV1
open FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1

noncomputable section

universe u

/-!
# Uniform staggered C-grid selection on a finite pair family

This is the package-free finite combinatorial layer.  Pointwise, the two
graph-C values of a pair select one of the staggered grids.  One label then
works for at least one third of the finite family.  On that fibre the two
independently normalised C-values agree, while each changes by at most `r`.
-/

/-- The C-value obtained by independently snapping `c` to its cell centre. -/
def threeShiftNormalizedC (r : Real) (k : Fin 3) (c : Real) : Real :=
  threeShiftCellCenter r k c

/-- A grid label is good for a pair precisely when its two C-values have the
same half-open cell code. -/
def GoodThreeShiftCGridPair
    (r leftC rightC : Real) (k : Fin 3) : Prop :=
  threeShiftFloorCode r k leftC = threeShiftFloorCode r k rightC

theorem exists_goodThreeShiftCGridPair
    {r leftC rightC : Real} (hr : 0 < r)
    (hgap : |leftC - rightC| ≤ r) :
    ∃ k : Fin 3, GoodThreeShiftCGridPair r leftC rightC k := by
  exact exists_same_threeShiftFloorCode hr hgap

theorem goodThreeShiftCGridPair_normalized_eq
    {r leftC rightC : Real} {k : Fin 3}
    (hgood : GoodThreeShiftCGridPair r leftC rightC k) :
    threeShiftNormalizedC r k leftC =
      threeShiftNormalizedC r k rightC := by
  exact threeShiftCellCenter_eq_of_code_eq hgood

theorem abs_sub_threeShiftNormalizedC_le
    {r c : Real} (hr : 0 < r) (k : Fin 3) :
    |c - threeShiftNormalizedC r k c| ≤ r := by
  exact abs_sub_threeShiftCellCenter_le hr k

/-- Pigeonhole the pointwise staggered-grid choices.  The returned carrier is
literal `threeShiftFiber`, hence is a subset without any quotienting or
cross-code multiplicity. -/
theorem exists_uniform_threeShiftCGrid_fiber
    {alpha : Type u} [DecidableEq alpha]
    (items : Finset alpha) (leftC rightC : alpha -> Real)
    {r : Real} (hr : 0 < r) (hitems : items.Nonempty)
    (hgap : forall a, a ∈ items -> |leftC a - rightC a| ≤ r) :
    ∃ (k : Fin 3) (fiber : Finset alpha),
      fiber.Nonempty ∧
      fiber ⊆ items ∧
      items.card ≤ 3 * fiber.card ∧
      (forall a, a ∈ fiber ->
        GoodThreeShiftCGridPair r (leftC a) (rightC a) k) ∧
      (forall a, a ∈ fiber ->
        threeShiftNormalizedC r k (leftC a) =
          threeShiftNormalizedC r k (rightC a)) ∧
      (forall a, a ∈ fiber ->
        |leftC a - threeShiftNormalizedC r k (leftC a)| ≤ r) ∧
      (forall a, a ∈ fiber ->
        |rightC a - threeShiftNormalizedC r k (rightC a)| ≤ r) := by
  let good : alpha -> Fin 3 -> Prop := fun a k =>
    GoodThreeShiftCGridPair r (leftC a) (rightC a) k
  have hgood : forall a, a ∈ items -> ∃ k : Fin 3, good a k := by
    intro a ha
    exact exists_goodThreeShiftCGridPair hr (hgap a ha)
  obtain ⟨k, hfiber, hcard, hfiberGood⟩ :=
    exists_uniform_threeShift_fiber items good hitems hgood
  let fiber := threeShiftFiber items
    (chosenThreeShiftLabel items good hgood) k
  refine ⟨k, fiber, hfiber, ?_, hcard, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (mem_threeShiftFiber_iff items
      (chosenThreeShiftLabel items good hgood) k a).mp ha |>.1
  · intro a ha
    exact hfiberGood a ha
  · intro a ha
    exact goodThreeShiftCGridPair_normalized_eq (hfiberGood a ha)
  · intro _a _ha
    exact abs_sub_threeShiftNormalizedC_le hr k
  · intro _a _ha
    exact abs_sub_threeShiftNormalizedC_le hr k

/-- For a fixed grid label, independently transforming the left objects is an
image of the original left carrier and therefore never increases its card. -/
theorem image_threeShiftNormalized_left_card_le
    {alpha : Type u} {beta : Type*}
    [DecidableEq alpha] [DecidableEq beta]
    (items : Finset alpha) (transform : Fin 3 -> alpha -> beta) (k : Fin 3) :
    (items.image (transform k)).card ≤ items.card := by
  exact Finset.card_image_le

/-- The analogous no-multiplicity bound for the independently transformed
right carrier. -/
theorem image_threeShiftNormalized_right_card_le
    {alpha : Type u} {beta : Type*}
    [DecidableEq alpha] [DecidableEq beta]
    (items : Finset alpha) (transform : Fin 3 -> alpha -> beta) (k : Fin 3) :
    (items.image (transform k)).card ≤ items.card := by
  exact Finset.card_image_le

#print axioms exists_goodThreeShiftCGridPair
#print axioms exists_uniform_threeShiftCGrid_fiber
#print axioms image_threeShiftNormalized_left_card_le
#print axioms image_threeShiftNormalized_right_card_le

end

end FamilyStickyCinematicL32ThreeShiftCGridPigeonholeV1
