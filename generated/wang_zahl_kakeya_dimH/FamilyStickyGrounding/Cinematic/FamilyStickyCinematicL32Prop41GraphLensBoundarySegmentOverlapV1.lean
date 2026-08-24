import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GraphLensRegionV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1

open FamilyStickyCinematicL32Prop41GraphLensRegionV1

/-!
# Positive-length boundary overlap for graph lenses

PYZ Definition 4.5 uses the Marcus--Tardos notion of overlapping lenses:
two simple closed lens boundaries overlap when they share a curve segment
of positive length.  For graph lenses inside the original strip, such a
segment is represented faithfully by a graph arc over a nondegenerate
closed parameter interval.
-/

/-- Two planar boundary sets share a positive-length graph segment. -/
def sharePositiveGraphSegment
    (E F : Set (Real × Real)) : Prop :=
  exists g : Real -> Real, exists a b : Real,
    a < b ∧ graphArc g (Icc a b) ⊆ E ∩ F

/-- Shared-positive-segment is symmetric. -/
theorem sharePositiveGraphSegment_symm
    {E F : Set (Real × Real)}
    (h : sharePositiveGraphSegment E F) :
    sharePositiveGraphSegment F E := by
  rcases h with ⟨g, a, b, hab, hsegment⟩
  exact ⟨g, a, b, hab, fun q hq => (hsegment hq).symm⟩

/-- Every nondegenerate graph lens boundary shares a positive-length graph
segment with itself. -/
theorem graphLensBoundaryArcs_sharePositiveGraphSegment_self
    (g h : Real -> Real) {thetaLeft thetaRight : Real}
    (horder : thetaLeft < thetaRight) :
    sharePositiveGraphSegment
      (graphLensBoundaryArcs g h thetaLeft thetaRight)
      (graphLensBoundaryArcs g h thetaLeft thetaRight) := by
  refine ⟨g, thetaLeft, thetaRight, horder, ?_⟩
  intro q hq
  exact ⟨Or.inl hq, Or.inl hq⟩

/-- A positive shared boundary segment gives a literal point common to the
two filled graph-lens regions. -/
theorem verticalRegions_overlap_of_boundaryArcs_sharePositiveGraphSegment
    (g1 h1 g2 h2 : Real -> Real)
    (theta1Left theta1Right theta2Left theta2Right : Real)
    (hoverlap : sharePositiveGraphSegment
      (graphLensBoundaryArcs g1 h1 theta1Left theta1Right)
      (graphLensBoundaryArcs g2 h2 theta2Left theta2Right)) :
    (graphLensVerticalRegion g1 h1 theta1Left theta1Right ∩
      graphLensVerticalRegion g2 h2 theta2Left theta2Right).Nonempty := by
  rcases hoverlap with ⟨g, a, b, hab, hsegment⟩
  have hpointArc : (g a, a) ∈ graphArc g (Icc a b) :=
    ⟨⟨le_rfl, le_of_lt hab⟩, rfl⟩
  have hpointBoundary := hsegment hpointArc
  exact ⟨(g a, a),
    graphLensBoundaryArcs_subset_verticalRegion _ _ _ _
      hpointBoundary.1,
    graphLensBoundaryArcs_subset_verticalRegion _ _ _ _
      hpointBoundary.2⟩

/-- Therefore Marcus--Tardos positive-segment overlap forces overlap of the
exact parameter supports of the two graph lenses. -/
theorem rootSupports_overlap_of_boundaryArcs_sharePositiveGraphSegment
    (g1 h1 g2 h2 : Real -> Real)
    (theta1Left theta1Right theta2Left theta2Right : Real)
    (hoverlap : sharePositiveGraphSegment
      (graphLensBoundaryArcs g1 h1 theta1Left theta1Right)
      (graphLensBoundaryArcs g2 h2 theta2Left theta2Right)) :
    (Icc theta1Left theta1Right ∩
      Icc theta2Left theta2Right).Nonempty := by
  exact rootSupports_overlap_of_verticalRegions_overlap
    g1 h1 g2 h2 theta1Left theta1Right theta2Left theta2Right
    (verticalRegions_overlap_of_boundaryArcs_sharePositiveGraphSegment
      g1 h1 g2 h2 theta1Left theta1Right theta2Left theta2Right hoverlap)

#print axioms sharePositiveGraphSegment
#print axioms sharePositiveGraphSegment_symm
#print axioms graphLensBoundaryArcs_sharePositiveGraphSegment_self
#print axioms verticalRegions_overlap_of_boundaryArcs_sharePositiveGraphSegment
#print axioms rootSupports_overlap_of_boundaryArcs_sharePositiveGraphSegment

end FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1
