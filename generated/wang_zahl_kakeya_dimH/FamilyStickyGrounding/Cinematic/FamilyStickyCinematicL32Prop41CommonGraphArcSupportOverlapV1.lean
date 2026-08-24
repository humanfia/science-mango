import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41CommonGraphArcSupportOverlapV1

open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1

/-!
# Open support overlap forces a shared positive graph segment

This is the converse needed only when two lens boundaries literally contain
arcs of the same graph.  It does not assert a converse for arbitrary planar
boundaries.
-/

theorem sharePositiveGraphSegment_of_common_graphArc_Ioo_inter_nonempty
    (g : Real -> Real) {E F : Set (Real × Real)}
    {leftE rightE leftF rightF : Real}
    (hE : graphArc g (Icc leftE rightE) ⊆ E)
    (hF : graphArc g (Icc leftF rightF) ⊆ F)
    (hoverlap : (Ioo leftE rightE ∩ Ioo leftF rightF).Nonempty) :
    sharePositiveGraphSegment E F := by
  rcases hoverlap with ⟨theta, hthetaE, hthetaF⟩
  refine ⟨g, theta, min rightE rightF, lt_min hthetaE.2 hthetaF.2, ?_⟩
  intro q hq
  have hqE : q ∈ graphArc g (Icc leftE rightE) := by
    refine ⟨⟨hthetaE.1.le.trans hq.1.1,
      hq.1.2.trans (min_le_left rightE rightF)⟩, hq.2⟩
  have hqF : q ∈ graphArc g (Icc leftF rightF) := by
    refine ⟨⟨hthetaF.1.le.trans hq.1.1,
      hq.1.2.trans (min_le_right rightE rightF)⟩, hq.2⟩
  exact ⟨hE hqE, hF hqF⟩

theorem graphLensBoundaryArcs_sharePositiveGraphSegment_of_common_firstArc
    (g hE hF : Real -> Real)
    {leftE rightE leftF rightF : Real}
    (hoverlap : (Ioo leftE rightE ∩ Ioo leftF rightF).Nonempty) :
    sharePositiveGraphSegment
      (graphLensBoundaryArcs g hE leftE rightE)
      (graphLensBoundaryArcs g hF leftF rightF) := by
  exact sharePositiveGraphSegment_of_common_graphArc_Ioo_inter_nonempty g
    (fun _ hq => Or.inl hq) (fun _ hq => Or.inl hq) hoverlap

#print axioms sharePositiveGraphSegment_of_common_graphArc_Ioo_inter_nonempty
#print axioms graphLensBoundaryArcs_sharePositiveGraphSegment_of_common_firstArc

end FamilyStickyCinematicL32Prop41CommonGraphArcSupportOverlapV1
