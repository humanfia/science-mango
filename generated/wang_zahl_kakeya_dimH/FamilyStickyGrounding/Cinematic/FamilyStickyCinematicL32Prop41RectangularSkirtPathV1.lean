import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CircleLiftEmbeddingV1
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

open Function Set

namespace FamilyStickyCinematicL32Prop41RectangularSkirtPathV1

open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1

noncomputable section

/-!
# Literal six-piece path for the PYZ rectangular skirt

The graph and five axis-aligned skirt pieces are built as bundled Mathlib
paths.  Concatenation provides continuity and the range theorem below proves
that no carrier has been changed.  Simplicity/injectivity is deliberately
separated into the next geometric module.
-/

/-- A graph arc, parametrized monotonically by its parameter coordinate. -/
noncomputable def graphPath
    (f : Real -> Real) (A B : Real) (hAB : A <= B)
    (hf : ContinuousOn f (Icc A B)) :
    Path (f A, A) (f B, B) :=
  (Path.segment A B).map' (by
    rw [Path.range_segment, segment_eq_Icc hAB]
    exact hf.prodMk continuousOn_id)

/-- The graph path has exactly the intended graph-arc range. -/
theorem range_graphPath
    (f : Real -> Real) (A B : Real) (hAB : A <= B)
    (hf : ContinuousOn f (Icc A B)) :
    range (graphPath f A B hAB hf) = graphArc f (Icc A B) := by
  rw [graphPath]
  change range ((fun theta : Real => (f theta, theta)) ∘ Path.segment A B) = _
  rw [Set.range_comp, Path.range_segment, segment_eq_Icc hAB]
  ext q
  constructor
  · rintro ⟨theta, htheta, rfl⟩
    exact ⟨htheta, rfl⟩
  · rintro ⟨htheta, hvalue⟩
    exact ⟨q.2, htheta, Prod.ext hvalue.symm rfl⟩

/-- A vertical skirt segment, with arbitrary orientation. -/
noncomputable def verticalPath (theta y0 y1 : Real) :
    Path (y0, theta) (y1, theta) :=
  (Path.segment y0 y1).map (by fun_prop :
    Continuous fun y : Real => (y, theta))

/-- The vertical path has exactly the unordered vertical segment as range. -/
theorem range_verticalPath (theta y0 y1 : Real) :
    range (verticalPath theta y0 y1) =
      verticalSegment theta y0 y1 := by
  rw [verticalPath]
  change range ((fun y : Real => (y, theta)) ∘ Path.segment y0 y1) = _
  rw [Set.range_comp, Path.range_segment, segment_eq_uIcc]
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨rfl, hy⟩
  · rintro ⟨htheta, hy⟩
    exact ⟨q.1, hy, Prod.ext rfl htheta.symm⟩

/-- Bottom height used by the literal skirt. -/
def skirtBottom (M depth : Real) : Real := -M - depth

/-- The bundled six-piece skirt path: graph, right top, right wall, bottom,
left wall, left top. -/
noncomputable def rectangularSkirtPath
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A <= B) (hdepth : 0 <= depth)
    (hf : ContinuousOn f (Icc A B)) :
    Path (f A, A) (f A, A) :=
  (((((graphPath f A B hAB hf).trans
      (graphPath (fun _ => f B) B (B + depth)
        (le_add_of_nonneg_right hdepth) continuousOn_const)).trans
      (verticalPath (B + depth) (f B) (skirtBottom M depth))).trans
      (graphPath (fun _ => skirtBottom M depth) (A - depth) (B + depth)
        (by linarith) continuousOn_const).symm).trans
      (verticalPath (A - depth) (skirtBottom M depth) (f A))).trans
      (graphPath (fun _ => f A) (A - depth) A
        (sub_le_self _ hdepth) continuousOn_const)

/-- Repeated path-range union gives exactly the literal set-level skirt. -/
theorem range_rectangularSkirtPath
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A <= B) (hdepth : 0 <= depth)
    (hf : ContinuousOn f (Icc A B)) :
    range (rectangularSkirtPath f A B M depth hAB hdepth hf) =
      rectangularSkirtCurve f A B M depth := by
  simp only [rectangularSkirtPath, Path.trans_range, Path.symm_range,
    range_graphPath, range_verticalPath]
  simp only [skirtBottom]
  rw [show verticalSegment (B + depth) (f B) (-M - depth) =
      verticalSegment (B + depth) (-M - depth) (f B) by
    simp only [verticalSegment, uIcc_comm]]
  ext q
  simp only [rectangularSkirtCurve, mem_union]
  tauto

/-- Extend the bundled skirt path to a globally continuous scalar loop. -/
noncomputable def rectangularSkirtLoop
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A <= B) (hdepth : 0 <= depth)
    (hf : ContinuousOn f (Icc A B)) : Real -> Real × Real :=
  (rectangularSkirtPath f A B M depth hAB hdepth hf).extend

/-- A closed bundled path still has its full range after restricting the
extended scalar parametrization to `[0,1)`: the omitted endpoint repeats
the included initial point. -/
theorem image_extend_Ico_of_closedPath
    {X : Type*} [TopologicalSpace X] {x : X} (gamma : Path x x) :
    gamma.extend '' Ico (0 : Real) 1 = range gamma := by
  apply Subset.antisymm
  · exact (image_subset_range _ _).trans_eq gamma.extend_range
  · rintro y ⟨t, rfl⟩
    by_cases ht : (t : Real) < 1
    · refine ⟨t, ⟨t.2.1, ht⟩, ?_⟩
      exact gamma.extend_extends' t
    · have ht1 : (t : Real) = 1 := le_antisymm t.2.2 (not_lt.mp ht)
      refine ⟨0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
      rw [show t = (1 : unitInterval) from Subtype.ext ht1]
      simp

/-- The scalar skirt loop is globally continuous. -/
theorem continuous_rectangularSkirtLoop
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A <= B) (hdepth : 0 <= depth)
    (hf : ContinuousOn f (Icc A B)) :
    Continuous (rectangularSkirtLoop f A B M depth hAB hdepth hf) :=
  Path.continuous_extend
    (rectangularSkirtPath f A B M depth hAB hdepth hf)

/-- The scalar loop closes at the endpoints of its fundamental interval. -/
theorem rectangularSkirtLoop_zero_eq_one
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A <= B) (hdepth : 0 <= depth)
    (hf : ContinuousOn f (Icc A B)) :
    rectangularSkirtLoop f A B M depth hAB hdepth hf 0 =
      rectangularSkirtLoop f A B M depth hAB hdepth hf 1 := by
  simp [rectangularSkirtLoop]

/-- The half-open scalar-loop image is definitionally faithful to the
original literal rectangular-skirt carrier. -/
theorem image_rectangularSkirtLoop_Ico
    (f : Real -> Real) (A B M depth : Real)
    (hAB : A <= B) (hdepth : 0 <= depth)
    (hf : ContinuousOn f (Icc A B)) :
    rectangularSkirtLoop f A B M depth hAB hdepth hf '' Ico 0 1 =
      rectangularSkirtCurve f A B M depth := by
  rw [rectangularSkirtLoop, image_extend_Ico_of_closedPath,
    range_rectangularSkirtPath]

#print axioms graphPath
#print axioms range_graphPath
#print axioms verticalPath
#print axioms range_verticalPath
#print axioms rectangularSkirtPath
#print axioms range_rectangularSkirtPath
#print axioms rectangularSkirtLoop
#print axioms image_extend_Ico_of_closedPath
#print axioms continuous_rectangularSkirtLoop
#print axioms rectangularSkirtLoop_zero_eq_one
#print axioms image_rectangularSkirtLoop_Ico

end

end FamilyStickyCinematicL32Prop41RectangularSkirtPathV1
