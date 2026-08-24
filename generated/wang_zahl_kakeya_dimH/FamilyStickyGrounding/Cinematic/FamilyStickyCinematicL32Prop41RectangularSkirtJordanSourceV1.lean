import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FourLensCodeRealizationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41GraphLensRegionV1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Maps.Basic

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1

open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41GraphLensRegionV1
open FamilyStickyCinematicL32Prop41FourLensCodeRealizationV1

noncomputable section

/-!
# Exact Jordan/pseudo-circle source interface for the PYZ rectangular skirt

Mathlib currently has no packaged Jordan-curve or simple-closed-curve API.
This module therefore records the exact topology needed by PYZ Section 4:
a closed Jordan curve is the range of an embedding of the unit circle, and
proper intersection means alternating points on every sufficiently small
centered circle.  The rectangular-skirt carrier is defined literally.

The final source structure lists precisely what remains to prove about that
carrier from A2--A3.  It does not assume a lens count or a rectangle bound.
-/

/-- The Euclidean unit circle used as the source of a Jordan embedding. -/
abbrev PlaneUnitCircle :=
  {q : Real × Real // q.1 ^ 2 + q.2 ^ 2 = 1}

/-- A closed Jordan plane curve, literally the range of an embedding of the
unit circle. -/
def IsClosedJordanCurve (E : Set (Real × Real)) : Prop :=
  exists e : PlaneUnitCircle -> Real × Real,
    Topology.IsEmbedding e ∧ range e = E

/-- Polar point on the Euclidean circle centered at `p`. -/
def planeCirclePoint (p : Real × Real) (r theta : Real) :
    Real × Real :=
  (p.1 + r * Real.cos theta, p.2 + r * Real.sin theta)

/-- Euclidean circle in the `(value, parameter)` plane. -/
def planeCircle (p : Real × Real) (r : Real) : Set (Real × Real) :=
  {q | (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 = r ^ 2}

/-- The intersections of `E` and `F` with one centered circle alternate in
counterclockwise cyclic order. -/
def CyclicallyAlternatesOnCircle
    (E F : Set (Real × Real)) (p : Real × Real) (r : Real) : Prop :=
  exists theta0 theta1 theta2 theta3 : Real,
    theta0 < theta1 ∧ theta1 < theta2 ∧ theta2 < theta3 ∧
    theta3 < theta0 + 2 * Real.pi ∧
    E ∩ planeCircle p r =
      {planeCirclePoint p r theta0, planeCirclePoint p r theta2} ∧
    F ∩ planeCircle p r =
      {planeCirclePoint p r theta1, planeCirclePoint p r theta3}

/-- PYZ proper intersection: alternation holds on every sufficiently small
circle about the intersection point. -/
def ProperPlaneCurveIntersectionAt
    (E F : Set (Real × Real)) (p : Real × Real) : Prop :=
  exists r0 : Real, 0 < r0 ∧ forall r : Real,
    0 < r -> r < r0 -> CyclicallyAlternatesOnCircle E F p r

/-- Literal pseudo-circle family from PYZ Section 4. -/
def IsPseudoCircleFamily
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (curveSet : FirstGenerationCurve curves -> Set (Real × Real)) : Prop :=
  (forall c, IsClosedJordanCurve (curveSet c)) ∧
  forall c d, c ≠ d ->
    (curveSet c ∩ curveSet d).ncard <= 2 ∧
    forall p, p ∈ curveSet c ∩ curveSet d ->
      ProperPlaneCurveIntersectionAt (curveSet c) (curveSet d) p

/-- A vertical segment at fixed parameter, with unordered value endpoints. -/
def verticalSegment (theta y0 y1 : Real) : Set (Real × Real) :=
  {q | q.2 = theta ∧ q.1 ∈ uIcc y0 y1}

/-- The literal rectangular-skirt extension from PYZ Section 4.  In the
paper's notation `depth=j` and the bottom value is `-M-j`. -/
def rectangularSkirtCurve
    (f : Real -> Real) (A B M depth : Real) : Set (Real × Real) :=
  graphArc f (Icc A B) ∪
  graphArc (fun _ => f A) (Icc (A - depth) A) ∪
  graphArc (fun _ => f B) (Icc B (B + depth)) ∪
  verticalSegment (A - depth) (-M - depth) (f A) ∪
  verticalSegment (B + depth) (-M - depth) (f B) ∪
  graphArc (fun _ => -M - depth) (Icc (A - depth) (B + depth))

/-- The original graph arc is literally contained in its skirt extension. -/
theorem graphArc_subset_rectangularSkirtCurve
    (f : Real -> Real) (A B M depth : Real) :
    graphArc f (Icc A B) ⊆ rectangularSkirtCurve f A B M depth := by
  intro q hq
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hq))))

/-- Restricting a graph arc to a smaller support preserves inclusion. -/
theorem graphArc_mono {g : Real -> Real} {S T : Set Real}
    (hST : S ⊆ T) : graphArc g S ⊆ graphArc g T := by
  intro q hq
  exact ⟨hST hq.1, hq.2⟩

/-- The actual inside-strip graph-lens boundary is contained in the union of
the two corresponding rectangular skirts. -/
theorem graphLensBoundaryArcs_subset_union_rectangularSkirts
    (g h : Real -> Real) {A B thetaLeft thetaRight M depthG depthH : Real}
    (hthetaLeft : thetaLeft ∈ Icc A B)
    (hthetaRight : thetaRight ∈ Icc A B) :
    graphLensBoundaryArcs g h thetaLeft thetaRight ⊆
      rectangularSkirtCurve g A B M depthG ∪
        rectangularSkirtCurve h A B M depthH := by
  have hrootInterval : Icc thetaLeft thetaRight ⊆ Icc A B := by
    intro theta htheta
    exact ⟨hthetaLeft.1.trans htheta.1,
      htheta.2.trans hthetaRight.2⟩
  intro q hq
  rcases hq with hq | hq
  · exact Or.inl (graphArc_subset_rectangularSkirtCurve g A B M depthG
      (graphArc_mono hrootInterval hq))
  · exact Or.inr (graphArc_subset_rectangularSkirtCurve h A B M depthH
      (graphArc_mono hrootInterval hq))

/-- Paper assumption A2: endpoint values are pairwise distinct at both ends
of the graph interval. -/
def EndpointValuesDistinct
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (graph : curve -> Real -> Real) (A B : Real) : Prop :=
  Set.InjOn (fun c => graph c A) (curves : Set curve) ∧
    Set.InjOn (fun c => graph c B) (curves : Set curve)

/-- Paper assumption A3: no distinct graph pair has equal value and equal
first derivative at one parameter. -/
def NoTangentialGraphIntersections
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (graph first : curve -> Real -> Real) (A B : Real) : Prop :=
  forall c, c ∈ curves -> forall d, d ∈ curves -> c ≠ d ->
    forall theta, theta ∈ Icc A B ->
      ¬ (graph c theta = graph d theta ∧
        first c theta = first d theta)

/-- At-most-two intersection input supplied by the cinematic two-zero
lemma, before closing the graphs by skirts. -/
def GraphPairsIntersectAtMostTwice
    {curve : Type*} [DecidableEq curve] (curves : Finset curve)
    (graph : curve -> Real -> Real) (A B : Real) : Prop :=
  forall c, c ∈ curves -> forall d, d ∈ curves -> c ≠ d ->
    {theta | theta ∈ Icc A B ∧ graph c theta = graph d theta}.ncard <= 2

/-- Exact residual Jordan source for the rectangular-skirt construction.
The elementary carrier is definitionally fixed above.  What remains is to
prove that every skirt is a circle embedding, that no new pair intersections
are created outside the original graph arcs, and that A3 gives proper
alternation at every retained crossing. -/
structure RectangularSkirtJordanSource
    {curve : Type*} [DecidableEq curve]
    (curves : Finset curve) (graph first : curve -> Real -> Real)
    (A B M : Real) where
  depth : FirstGenerationCurve curves -> Real
  depth_pos : forall c, 0 < depth c
  depth_injective : Function.Injective depth
  graph_bound : forall c, forall theta, theta ∈ Icc A B ->
    |graph c theta| <= M
  endpoint_distinct : EndpointValuesDistinct curves graph A B
  graph_atMostTwo : GraphPairsIntersectAtMostTwice curves graph A B
  no_tangential_intersections :
    NoTangentialGraphIntersections curves graph first A B
  skirt_isJordan : forall c,
    IsClosedJordanCurve
      (rectangularSkirtCurve (graph c.1) A B M (depth c))
  skirt_pair_atMostTwo : forall c d, c ≠ d ->
    (rectangularSkirtCurve (graph c.1) A B M (depth c) ∩
      rectangularSkirtCurve (graph d.1) A B M (depth d)).ncard <= 2
  skirt_pair_proper : forall c d, c ≠ d -> forall p,
    p ∈ rectangularSkirtCurve (graph c.1) A B M (depth c) ∩
      rectangularSkirtCurve (graph d.1) A B M (depth d) ->
    ProperPlaneCurveIntersectionAt
      (rectangularSkirtCurve (graph c.1) A B M (depth c))
      (rectangularSkirtCurve (graph d.1) A B M (depth d)) p

/-- The literal skirt carrier associated to a Jordan source. -/
def RectangularSkirtJordanSource.curveSet
    {curve : Type*} [DecidableEq curve]
    {curves : Finset curve} {graph first : curve -> Real -> Real}
    {A B M : Real}
    (S : RectangularSkirtJordanSource curves graph first A B M)
    (c : FirstGenerationCurve curves) : Set (Real × Real) :=
  rectangularSkirtCurve (graph c.1) A B M (S.depth c)

/-- The exact residual source fields package into the PYZ pseudo-circle
property; no MT cardinality estimate is involved. -/
theorem RectangularSkirtJordanSource.isPseudoCircleFamily
    {curve : Type*} [DecidableEq curve]
    {curves : Finset curve} {graph first : curve -> Real -> Real}
    {A B M : Real}
    (S : RectangularSkirtJordanSource curves graph first A B M) :
    IsPseudoCircleFamily curves S.curveSet := by
  refine ⟨S.skirt_isJordan, ?_⟩
  intro c d hcd
  exact ⟨S.skirt_pair_atMostTwo c d hcd,
    S.skirt_pair_proper c d hcd⟩

/-- Add the oriented two-arc decompositions needed by the finite `Fin 4`
realization layer. -/
structure RectangularSkirtFourCodeSource
    {curve : Type*} [DecidableEq curve]
    (curves : Finset curve) (graph first : curve -> Real -> Real)
    (A B M : Real)
    extends RectangularSkirtJordanSource curves graph first A B M where
  pairData : forall p : FirstGenerationCurvePair curves,
    OrientedTwoArcPairRealization curves toRectangularSkirtJordanSource.curveSet p

#print axioms PlaneUnitCircle
#print axioms IsClosedJordanCurve
#print axioms CyclicallyAlternatesOnCircle
#print axioms ProperPlaneCurveIntersectionAt
#print axioms IsPseudoCircleFamily
#print axioms rectangularSkirtCurve
#print axioms graphArc_subset_rectangularSkirtCurve
#print axioms graphLensBoundaryArcs_subset_union_rectangularSkirts
#print axioms EndpointValuesDistinct
#print axioms NoTangentialGraphIntersections
#print axioms GraphPairsIntersectAtMostTwice
#print axioms RectangularSkirtJordanSource
#print axioms RectangularSkirtJordanSource.isPseudoCircleFamily
#print axioms RectangularSkirtFourCodeSource

end

end FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
