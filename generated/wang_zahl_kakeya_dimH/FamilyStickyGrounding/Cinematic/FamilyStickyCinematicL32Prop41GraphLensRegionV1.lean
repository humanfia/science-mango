import Mathlib.Data.Real.Basic

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41GraphLensRegionV1

/-!
# Set-level realization of a first-generation graph lens

This is the minimal planar carrier needed before the Jordan-curve layer of
PYZ Proposition 4.1.  Between two ordered intersection parameters, the lens
is the closed vertical region between the two graph arcs.  Its parameter
projection, and the projection of its two designated boundary arcs, are
proved to be exactly the closed root interval.
-/

/-- One graph arc over a prescribed parameter support. -/
def graphArc (g : Real -> Real) (support : Set Real) :
    Set (Real × Real) :=
  {q | q.2 ∈ support ∧ q.1 = g q.2}

/-- The closed vertical region between two graphs over the interval between
two intersection parameters. -/
def graphLensVerticalRegion (g h : Real -> Real)
    (thetaLeft thetaRight : Real) : Set (Real × Real) :=
  {q | q.2 ∈ Icc thetaLeft thetaRight ∧
    min (g q.2) (h q.2) <= q.1 ∧ q.1 <= max (g q.2) (h q.2)}

/-- The two graph arcs designated as the set-level lens boundary.  This is
not yet a claim about the topological boundary or a Jordan curve. -/
def graphLensBoundaryArcs (g h : Real -> Real)
    (thetaLeft thetaRight : Real) : Set (Real × Real) :=
  graphArc g (Icc thetaLeft thetaRight) ∪
    graphArc h (Icc thetaLeft thetaRight)

/-- Projection of a planar set to its parameter coordinate. -/
def parameterProjection (E : Set (Real × Real)) : Set Real :=
  Prod.snd '' E

/-- The planar lens region has precisely the root interval as parameter
projection. -/
theorem parameterProjection_graphLensVerticalRegion
    (g h : Real -> Real) (thetaLeft thetaRight : Real) :
    parameterProjection
        (graphLensVerticalRegion g h thetaLeft thetaRight) =
      Icc thetaLeft thetaRight := by
  ext theta
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.1
  · intro htheta
    refine ⟨(g theta, theta), ?_, rfl⟩
    exact ⟨htheta, min_le_left _ _, le_max_left _ _⟩

/-- The union of the two designated graph arcs also projects onto the full
root interval. -/
theorem parameterProjection_graphLensBoundaryArcs
    (g h : Real -> Real) (thetaLeft thetaRight : Real) :
    parameterProjection (graphLensBoundaryArcs g h thetaLeft thetaRight) =
      Icc thetaLeft thetaRight := by
  ext theta
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with hq | hq <;> exact hq.1
  · intro htheta
    refine ⟨(g theta, theta), ?_, rfl⟩
    exact Or.inl ⟨htheta, rfl⟩

/-- Both designated graph arcs lie in the vertical lens region. -/
theorem graphLensBoundaryArcs_subset_verticalRegion
    (g h : Real -> Real) (thetaLeft thetaRight : Real) :
    graphLensBoundaryArcs g h thetaLeft thetaRight ⊆
      graphLensVerticalRegion g h thetaLeft thetaRight := by
  intro q hq
  rcases hq with hq | hq
  · rcases hq with ⟨hqSupport, hqGraph⟩
    refine ⟨hqSupport, ?_, ?_⟩
    · rw [hqGraph]
      exact min_le_left _ _
    · rw [hqGraph]
      exact le_max_left _ _
  · rcases hq with ⟨hqSupport, hqGraph⟩
    refine ⟨hqSupport, ?_, ?_⟩
    · rw [hqGraph]
      exact min_le_right _ _
    · rw [hqGraph]
      exact le_max_right _ _

/-- Equal graph values at the left root make the two designated arcs share
their left endpoint. -/
theorem common_left_endpoint_mem_both_graphArcs
    (g h : Real -> Real) {thetaLeft thetaRight : Real}
    (horder : thetaLeft <= thetaRight)
    (hroot : g thetaLeft = h thetaLeft) :
    (g thetaLeft, thetaLeft) ∈
        graphArc g (Icc thetaLeft thetaRight) ∩
          graphArc h (Icc thetaLeft thetaRight) := by
  exact ⟨⟨⟨le_rfl, horder⟩, rfl⟩,
    ⟨⟨le_rfl, horder⟩, hroot⟩⟩

/-- Equal graph values at the right root make the two designated arcs share
their right endpoint. -/
theorem common_right_endpoint_mem_both_graphArcs
    (g h : Real -> Real) {thetaLeft thetaRight : Real}
    (horder : thetaLeft <= thetaRight)
    (hroot : g thetaRight = h thetaRight) :
    (g thetaRight, thetaRight) ∈
        graphArc g (Icc thetaLeft thetaRight) ∩
          graphArc h (Icc thetaLeft thetaRight) := by
  exact ⟨⟨⟨horder, le_rfl⟩, rfl⟩,
    ⟨⟨horder, le_rfl⟩, hroot⟩⟩

/-- An ordered root pair gives a nonempty planar lens region. -/
theorem graphLensVerticalRegion_nonempty_of_le
    (g h : Real -> Real) {thetaLeft thetaRight : Real}
    (horder : thetaLeft <= thetaRight) :
    (graphLensVerticalRegion g h thetaLeft thetaRight).Nonempty := by
  exact ⟨(g thetaLeft, thetaLeft),
    ⟨⟨le_rfl, horder⟩, min_le_left _ _, le_max_left _ _⟩⟩

/-- Planar overlap of two graph-lens regions forces overlap of their exact
root-support intervals. -/
theorem rootSupports_overlap_of_verticalRegions_overlap
    (g1 h1 g2 h2 : Real -> Real)
    (theta1Left theta1Right theta2Left theta2Right : Real)
    (hoverlap :
      (graphLensVerticalRegion g1 h1 theta1Left theta1Right ∩
        graphLensVerticalRegion g2 h2 theta2Left theta2Right).Nonempty) :
    (Icc theta1Left theta1Right ∩
      Icc theta2Left theta2Right).Nonempty := by
  rcases hoverlap with ⟨q, hq1, hq2⟩
  exact ⟨q.2, hq1.1, hq2.1⟩

#print axioms graphArc
#print axioms graphLensVerticalRegion
#print axioms graphLensBoundaryArcs
#print axioms parameterProjection_graphLensVerticalRegion
#print axioms parameterProjection_graphLensBoundaryArcs
#print axioms graphLensBoundaryArcs_subset_verticalRegion
#print axioms common_left_endpoint_mem_both_graphArcs
#print axioms common_right_endpoint_mem_both_graphArcs
#print axioms graphLensVerticalRegion_nonempty_of_le
#print axioms rootSupports_overlap_of_verticalRegions_overlap

end FamilyStickyCinematicL32Prop41GraphLensRegionV1
