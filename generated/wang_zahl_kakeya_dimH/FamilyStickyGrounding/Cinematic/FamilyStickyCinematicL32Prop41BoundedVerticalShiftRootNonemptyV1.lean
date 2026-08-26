import FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41BoundedVerticalShiftRootNonemptyV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

/-!
# A bounded continuous vertical shift produces a literal root

If two graph values lie in the same radius-`r` interval about an anchor,
their difference has size at most `2*r`.  Vertically shifting the second
graph by that exact difference makes the chosen parameter a root.

This is only the continuous real-shift nonemptiness step.  In particular it
does not replace the shift by one of three discrete values, prove
transversality or equal endpoint signs, or manufacture an exact two-root or
pair-local rectangle certificate.
-/

/-- Root carrier of an ordered graph pair after vertically shifting the
second graph by `shift`. -/
def verticallyShiftedRootSet (g h : Real -> Real)
    (shift A B : Real) : Set Real :=
  {theta | theta ∈ Icc A B ∧ g theta = h theta + shift}

/-- Two graph values close to one common anchor have a bounded vertical
shift for which the selected parameter is a literal root. -/
theorem exists_bounded_verticalShift_rootSet_nonempty_of_commonAnchor
    (g h : Real -> Real) {A B theta anchor r : Real}
    (htheta : theta ∈ Icc A B)
    (hg : |g theta - anchor| <= r)
    (hh : |h theta - anchor| <= r) :
    ∃ shift : Real,
      |shift| <= 2 * r ∧
      (verticallyShiftedRootSet g h shift A B).Nonempty := by
  refine ⟨g theta - h theta, ?_, ?_⟩
  · calc
      |g theta - h theta| <=
          |g theta - anchor| + |anchor - h theta| :=
        abs_sub_le (g theta) anchor (h theta)
      _ = |g theta - anchor| + |h theta - anchor| := by
        rw [abs_sub_comm anchor (h theta)]
      _ <= r + r := add_le_add hg hh
      _ = 2 * r := by ring
  · refine ⟨theta, htheta, ?_⟩
    ring

/-- Literal shifted root carrier for two actual tube graphs. -/
def actualTubeVerticallyShiftedRootSet
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    (shift A B : Real) : Set Real :=
  verticallyShiftedRootSet
    (cinematicTraceValue f
      (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T))
    (cinematicTraceValue f
      (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U))
    shift A B

/-- Actual-tube specialization of the common-anchor vertical-shift
producer. -/
theorem exists_bounded_verticalShift_actualTubeRootSet_nonempty_of_commonAnchor
    {radius : NNReal} (T U : Tube radius) (f : Real -> Real)
    {A B theta anchor r : Real}
    (htheta : theta ∈ Icc A B)
    (hT : |cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T) theta -
      anchor| <= r)
    (hU : |cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U) theta -
      anchor| <= r) :
    ∃ shift : Real,
      |shift| <= 2 * r ∧
      (actualTubeVerticallyShiftedRootSet T U f shift A B).Nonempty := by
  simpa only [actualTubeVerticallyShiftedRootSet] using
    exists_bounded_verticalShift_rootSet_nonempty_of_commonAnchor
      (cinematicTraceValue f
        (tubeGraphA T) (tubeGraphB T) (tubeGraphC T) (tubeGraphD T))
      (cinematicTraceValue f
        (tubeGraphA U) (tubeGraphB U) (tubeGraphC U) (tubeGraphD U))
      htheta hT hU

/-- The literal common-point value bounds in the high active geometry give
every ordered active tube pair a vertical shift of size at most four tube
radii with a nonempty shifted root carrier at that point's parameter. -/
theorem ActualCenteredHalfY1ActiveGeometryFacts.exists_activePair_bounded_verticalShift_rootSet_nonempty
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fine : UniformTubeFamily radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {E : Set (Real × Real)}
    {activeAtPoint : Real × Real -> Finset iota}
    {tubeAt : Real × Real -> Tube radius}
    {f f1 f2 : Real -> Real} {outerA outerB : Real}
    {hOuter : outerA <= outerB}
    {hf : forall z, HasDerivAt f (f1 z) z}
    {hf1 : forall z, HasDerivAt f1 (f2 z) z}
    {tGlobal globalDelta : Real}
    (G : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    {q : Real × Real} (hq : q ∈ E)
    {i j : iota} (hi : i ∈ activeAtPoint q)
    (hj : j ∈ activeAtPoint q)
    {A B : Real} (hqParameter : q.2 ∈ Icc A B) :
    ∃ shift : Real,
      |shift| <= 4 * (radius : Real) ∧
      (actualTubeVerticallyShiftedRootSet
        (fine.tubes i) (fine.tubes j) f shift A B).Nonempty := by
  have hT := G.hactiveFullWitness q hq i hi
  have hU := G.hactiveFullWitness q hq j hj
  obtain ⟨shift, hshift, hroot⟩ :=
    exists_bounded_verticalShift_actualTubeRootSet_nonempty_of_commonAnchor
      (fine.tubes i) (fine.tubes j) f hqParameter hT hU
  refine ⟨shift, ?_, hroot⟩
  nlinarith

#print axioms verticallyShiftedRootSet
#print axioms exists_bounded_verticalShift_rootSet_nonempty_of_commonAnchor
#print axioms actualTubeVerticallyShiftedRootSet
#print axioms exists_bounded_verticalShift_actualTubeRootSet_nonempty_of_commonAnchor
#print axioms ActualCenteredHalfY1ActiveGeometryFacts.exists_activePair_bounded_verticalShift_rootSet_nonempty

end

end FamilyStickyCinematicL32Prop41BoundedVerticalShiftRootNonemptyV1
