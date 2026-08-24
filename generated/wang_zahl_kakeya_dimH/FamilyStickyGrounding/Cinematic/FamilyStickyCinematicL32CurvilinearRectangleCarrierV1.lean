import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGraphTangencyCoreV1
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CurvilinearRectangleCarrierV1

open FamilyStickyCinematicL32RectangleTangencyV1

noncomputable section

/-!
# Concrete curvilinear rectangles and a common-container producer

This module follows Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Definitions 3.1--3.2.  A graph rectangle is a vertical graph neighborhood
over a closed base interval.  `leftGraphLambdaComparable` records a literal
common graph rectangle whose base has the exact enlarged scale
`sqrt (lambda * delta / t)` and whose vertical radius is `lambda * delta`.

The main theorem constructs that container from overlap of the bases and a
pointwise graph-closeness estimate.  Thus later incomparability arguments do
not take existence of a common rectangle as a callback.
-/

/-- A graph together with the closed interval supporting its curvilinear
rectangle.  The scale and thickness are supplied separately so the same
carrier can be enlarged. -/
structure GraphRectangle where
  graph : Real -> Real
  left : Real
  right : Real
  left_le_right : left <= right

/-- Closed base interval of a graph rectangle. -/
def GraphRectangle.base (R : GraphRectangle) : Set Real :=
  Icc R.left R.right

/-- Vertical `delta`-thick graph rectangle in `(value,parameter)`
coordinates. -/
def GraphRectangle.carrier (R : GraphRectangle) (delta : Real) :
    Set (Real × Real) :=
  cinematicVerticalNeighborhood R.graph R.base delta

/-- A sufficient, literal form of PYZ `lambda`-comparability: the union is
contained in a common `(lambda * delta,t)` rectangle centered on the first
graph.  Centering on the first graph ensures that the witness belongs to the
same function family whenever the first rectangle does. -/
def leftGraphLambdaComparable
    (R S : GraphRectangle) (delta t lambda : Real) : Prop :=
  exists containerLeft containerRight,
    containerRight - containerLeft =
      Real.sqrt (lambda * delta / t) ∧
    R.carrier delta ∪ S.carrier delta ⊆
      cinematicVerticalNeighborhood R.graph
        (Icc containerLeft containerRight) (lambda * delta)

/-- Two intervals sharing a point have hull length at most the sum of their
lengths. -/
theorem hull_length_le_sum_of_lengths_of_common_point
    (R S : GraphRectangle) {theta0 : Real}
    (hR : theta0 ∈ R.base) (hS : theta0 ∈ S.base) :
    max R.right S.right - min R.left S.left <=
      (R.right - R.left) + (S.right - S.left) := by
  have hcrossRS : R.left <= S.right := hR.1.trans hS.2
  have hcrossSR : S.left <= R.right := hS.1.trans hR.2
  by_cases hleft : R.left <= S.left
  · rw [min_eq_left hleft]
    by_cases hright : R.right <= S.right
    · rw [max_eq_right hright]
      linarith [R.left_le_right]
    · rw [max_eq_left (le_of_not_ge hright)]
      linarith [S.left_le_right]
  · rw [min_eq_right (le_of_not_ge hleft)]
    by_cases hright : R.right <= S.right
    · rw [max_eq_right hright]
      linarith [R.left_le_right]
    · rw [max_eq_left (le_of_not_ge hright)]
      linarith [S.left_le_right]

/-- If the two bases overlap, fit inside the enlarged base scale, and the
two graph values differ by at most `(lambda-1) * delta` on their union, then
an explicit common enlarged graph rectangle exists. -/
theorem leftGraphLambdaComparable_of_graph_close
    (R S : GraphRectangle) {delta t lambda : Real}
    (hdelta : 0 <= delta) (hlambda : 1 <= lambda)
    (htheta : exists theta0, theta0 ∈ R.base ∧ theta0 ∈ S.base)
    (hbaseScale : (R.right - R.left) + (S.right - S.left) <=
      Real.sqrt (lambda * delta / t))
    (hgraphClose : forall theta, theta ∈ R.base ∪ S.base ->
      |R.graph theta - S.graph theta| <= (lambda - 1) * delta) :
    leftGraphLambdaComparable R S delta t lambda := by
  rcases htheta with ⟨theta0, hthetaR, hthetaS⟩
  let containerLeft := min R.left S.left
  let containerLength := Real.sqrt (lambda * delta / t)
  let containerRight := containerLeft + containerLength
  have hhull : max R.right S.right - min R.left S.left <=
      containerLength :=
    (hull_length_le_sum_of_lengths_of_common_point
      R S hthetaR hthetaS).trans hbaseScale
  have hbaseR : R.base ⊆ Icc containerLeft containerRight := by
    intro theta htheta
    constructor
    · exact (min_le_left R.left S.left).trans htheta.1
    · calc
        theta <= R.right := htheta.2
        _ <= max R.right S.right := le_max_left _ _
        _ <= containerRight := by
          dsimp only [containerRight, containerLeft]
          linarith
  have hbaseS : S.base ⊆ Icc containerLeft containerRight := by
    intro theta htheta
    constructor
    · exact (min_le_right R.left S.left).trans htheta.1
    · calc
        theta <= S.right := htheta.2
        _ <= max R.right S.right := le_max_right _ _
        _ <= containerRight := by
          dsimp only [containerRight, containerLeft]
          linarith
  refine ⟨containerLeft, containerRight, ?_, ?_⟩
  · dsimp only [containerRight, containerLength]
    ring
  · intro q hq
    rcases hq with hqR | hqS
    · have hqR' : q.2 ∈ R.base ∧ |q.1 - R.graph q.2| <= delta := hqR
      exact ⟨hbaseR hqR'.1, hqR'.2.trans (by nlinarith)⟩
    · have hqS' : q.2 ∈ S.base ∧ |q.1 - S.graph q.2| <= delta := hqS
      refine ⟨hbaseS hqS'.1, ?_⟩
      have hclose := hgraphClose q.2 (Or.inr hqS'.1)
      calc
        |q.1 - R.graph q.2| =
            |(q.1 - S.graph q.2) +
              (S.graph q.2 - R.graph q.2)| := by
          ring_nf
        _ <= |q.1 - S.graph q.2| +
            |S.graph q.2 - R.graph q.2| := abs_add_le _ _
        _ = |q.1 - S.graph q.2| +
            |R.graph q.2 - S.graph q.2| := by
          rw [abs_sub_comm (S.graph q.2)]
        _ <= delta + (lambda - 1) * delta :=
          add_le_add hqS'.2 hclose
        _ = lambda * delta := by ring

#print axioms hull_length_le_sum_of_lengths_of_common_point
#print axioms leftGraphLambdaComparable_of_graph_close

end

end FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
