import Mathlib.Order.Interval.Set.Infinite
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41GraphLensBoundarySharedSideExtractionV1

open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1

/-!
# A shared graph-lens boundary segment forces a nonfinite cross-side intersection

This is the finite set-theoretic core behind the faithful PYZ boundary
non-overlap argument.  It makes no common-reference assumption: if the union
of two boundary graph arcs shares a nondegenerate graph segment with another
such union, then at least one of the four cross-side intersections is
nonfinite.
-/

private theorem graphArc_infinite_of_lt
    (g : Real -> Real) {a b : Real} (hab : a < b) :
    (graphArc g (Icc a b)).Infinite := by
  have hinterval : (Icc a b).Infinite := Set.Icc_infinite hab
  have hinj : Set.InjOn (fun theta : Real => (g theta, theta))
      (Icc a b) := by
    intro x _hx y _hy hxy
    exact congrArg Prod.snd hxy
  have himage :
      ((fun theta : Real => (g theta, theta)) '' Icc a b).Infinite :=
    (infinite_image_iff hinj).2 hinterval
  have heq : graphArc g (Icc a b) =
      (fun theta : Real => (g theta, theta)) '' Icc a b := by
    ext q
    constructor
    · rintro hq
      refine ⟨q.2, hq.1, ?_⟩
      exact Prod.ext hq.2.symm rfl
    · rintro ⟨theta, htheta, rfl⟩
      exact ⟨htheta, rfl⟩
  simpa [heq] using himage

/-- A nondegenerate shared segment cannot be covered by four finite
cross-side intersections. -/
theorem exists_nonfinite_cross_side_intersection_of_sharePositiveGraphSegment
    (g11 g12 g21 g22 : Real -> Real)
    (support1 support2 : Set Real)
    (hoverlap : sharePositiveGraphSegment
      (graphArc g11 support1 ∪ graphArc g12 support1)
      (graphArc g21 support2 ∪ graphArc g22 support2)) :
    (graphArc g11 support1 ∩ graphArc g21 support2).Infinite ∨
    (graphArc g11 support1 ∩ graphArc g22 support2).Infinite ∨
    (graphArc g12 support1 ∩ graphArc g21 support2).Infinite ∨
    (graphArc g12 support1 ∩ graphArc g22 support2).Infinite := by
  by_contra hnone
  simp only [not_or, not_infinite] at hnone
  rcases hnone with ⟨h11, h12, h21, h22⟩
  have h11Finite :
      (graphArc g11 support1 ∩ graphArc g21 support2).Finite :=
    h11
  have h12Finite :
      (graphArc g11 support1 ∩ graphArc g22 support2).Finite :=
    h12
  have h21Finite :
      (graphArc g12 support1 ∩ graphArc g21 support2).Finite :=
    h21
  have h22Finite :
      (graphArc g12 support1 ∩ graphArc g22 support2).Finite :=
    h22
  have hcrossFinite :
      ((graphArc g11 support1 ∩ graphArc g21 support2) ∪
       (graphArc g11 support1 ∩ graphArc g22 support2) ∪
       (graphArc g12 support1 ∩ graphArc g21 support2) ∪
       (graphArc g12 support1 ∩ graphArc g22 support2)).Finite :=
    ((h11Finite.union h12Finite).union h21Finite).union h22Finite
  have hboundaryFinite :
      ((graphArc g11 support1 ∪ graphArc g12 support1) ∩
       (graphArc g21 support2 ∪ graphArc g22 support2)).Finite := by
    apply hcrossFinite.subset
    intro q hq
    rcases hq.1 with hq11 | hq12 <;>
      rcases hq.2 with hq21 | hq22
    · exact Or.inl (Or.inl (Or.inl ⟨hq11, hq21⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hq11, hq22⟩))
    · exact Or.inl (Or.inr ⟨hq12, hq21⟩)
    · exact Or.inr ⟨hq12, hq22⟩
  rcases hoverlap with ⟨g, a, b, hab, hsegment⟩
  have hsegmentFinite : (graphArc g (Icc a b)).Finite :=
    hboundaryFinite.subset hsegment
  exact (graphArc_infinite_of_lt g hab) hsegmentFinite

#print axioms exists_nonfinite_cross_side_intersection_of_sharePositiveGraphSegment

end FamilyStickyCinematicL32Prop41GraphLensBoundarySharedSideExtractionV1
