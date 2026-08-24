import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RectangularSkirtPairIntersectionV1

set_option autoImplicit false

open Function Set

namespace FamilyStickyCinematicL32Prop41RectangularSkirtPairEncCardV1

open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41RectangularSkirtPieceIntersectionsV1
open FamilyStickyCinematicL32Prop41RectangularSkirtPairIntersectionV1

noncomputable section

/-!
# Genuine extended-cardinality bounds for a skirt pair

The graph--graph intersection is an injective image of the scalar root set.
Consequently the exact carrier equalities from the 25-case exterior audit
give a finite `encard <= 2` result.  In the endpoint-reversal branch the
scalar input is `encard <= 1`, leaving room for the unique exterior crossing.
-/

theorem skirtGraph_inter_skirtGraph_eq_image_rootSet
    (f g : Real -> Real) (A B : Real) :
    skirtGraph f A B ∩ skirtGraph g A B =
      (fun theta : Real => (f theta, theta)) ''
        {theta | theta ∈ Icc A B ∧ f theta = g theta} := by
  ext q
  constructor
  · rintro ⟨⟨hqI, hqf⟩, ⟨_, hqg⟩⟩
    refine ⟨q.2, ⟨hqI, hqf.symm.trans hqg⟩, ?_⟩
    exact Prod.ext hqf.symm rfl
  · rintro ⟨theta, ⟨htheta, hfg⟩, rfl⟩
    exact ⟨⟨htheta, rfl⟩, ⟨htheta, hfg⟩⟩

theorem skirtGraph_inter_skirtGraph_encard_eq_rootSet
    (f g : Real -> Real) (A B : Real) :
    (skirtGraph f A B ∩ skirtGraph g A B).encard =
      {theta | theta ∈ Icc A B ∧ f theta = g theta}.encard := by
  rw [skirtGraph_inter_skirtGraph_eq_image_rootSet]
  apply Injective.encard_image
  intro x y hxy
  exact congrArg Prod.snd hxy

theorem rectangularSkirtCurve_inter_encard_le_two_of_same_endpoint_order
    (f g : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (he : 0 < e) (hde : d < e)
    (hleft : f A < g A) (hright : f B < g B)
    (hfLower : forall theta, theta ∈ Icc A B -> -M <= f theta)
    (hgLower : forall theta, theta ∈ Icc A B -> -M <= g theta)
    (hroots : {theta | theta ∈ Icc A B ∧
      f theta = g theta}.encard <= 2) :
    (rectangularSkirtCurve f A B M d ∩
      rectangularSkirtCurve g A B M e).encard <= 2 := by
  rw [rectangularSkirtCurve_inter_eq_graph_inter_of_same_endpoint_order
    f g A B M d e hAB hd he hde hleft hright hfLower hgLower,
    skirtGraph_inter_skirtGraph_encard_eq_rootSet]
  exact hroots

theorem rectangularSkirtCurve_inter_encard_le_two_of_reversed_endpoint_order
    (f g : Real -> Real) (A B M d e : Real)
    (hAB : A < B) (hd : 0 < d) (he : 0 < e) (hde : d < e)
    (hleft : f A < g A) (hright : g B < f B)
    (hfLower : forall theta, theta ∈ Icc A B -> -M <= f theta)
    (hgLower : forall theta, theta ∈ Icc A B -> -M <= g theta)
    (hroots : {theta | theta ∈ Icc A B ∧
      f theta = g theta}.encard <= 1) :
    (rectangularSkirtCurve f A B M d ∩
      rectangularSkirtCurve g A B M e).encard <= 2 := by
  rw [rectangularSkirtCurve_inter_eq_graph_inter_union_singleton_of_reversed_endpoint_order
    f g A B M d e hAB hd he hde hleft hright hfLower hgLower]
  calc
    ((skirtGraph f A B ∩ skirtGraph g A B) ∪
        {(g B, B + d)}).encard <=
      (skirtGraph f A B ∩ skirtGraph g A B).encard +
        ({(g B, B + d)} : Set (Real × Real)).encard :=
      encard_union_le _ _
    _ = {theta | theta ∈ Icc A B ∧ f theta = g theta}.encard + 1 := by
      rw [skirtGraph_inter_skirtGraph_encard_eq_rootSet, encard_singleton]
    _ <= 1 + 1 := add_le_add hroots le_rfl
    _ = 2 := by norm_num

#print axioms skirtGraph_inter_skirtGraph_eq_image_rootSet
#print axioms skirtGraph_inter_skirtGraph_encard_eq_rootSet
#print axioms rectangularSkirtCurve_inter_encard_le_two_of_same_endpoint_order
#print axioms rectangularSkirtCurve_inter_encard_le_two_of_reversed_endpoint_order

end

end FamilyStickyCinematicL32Prop41RectangularSkirtPairEncCardV1
