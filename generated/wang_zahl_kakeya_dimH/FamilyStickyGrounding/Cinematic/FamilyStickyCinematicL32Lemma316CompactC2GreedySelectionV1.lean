import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1

noncomputable section

/-!
# Compact-C2 rectangle form of finite greedy selection

The existing compact-domain form of PYZ Lemma 3.15 supplies the cardinality
of every closed comparability neighbourhood once that neighbourhood is put
in one enlarged rectangle.  The theorem below then invokes the independently
proved largest-mass greedy selection, retaining arbitrary vertex data rather
than replacing vertices by bare rectangles.

Consequently label incidences, survivor witnesses, and common-fine proofs
stored in the vertex type survive by literal `Finset` inclusion.
-/

universe u

/-- The explicit Lemma 3.15 bound used as the closed-neighbourhood loss in
the greedy argument. -/
def pyzClosedNeighbourBound (lambda : Real) : ENNReal :=
  ENNReal.ofReal (20 * lambda + 1) *
    (ENNReal.ofReal lambda * ENNReal.ofReal (Real.sqrt lambda))

/-- A directed container whose graph is the first rectangle can be lifted
to the compact-C2 relation when that first rectangle already lies in the
common C2 ball.  This is the contrapositive bridge required by the existing
Lemma 3.15 packing API. -/
theorem compactC2SymmetricGraphLambdaComparableOn_of_left
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta t lambda : Real}
    (hR : InPointwiseC2BallOn domain center R (3 * t))
    (hleft : leftGraphLambdaComparable
      R.rectangle S.rectangle delta t lambda) :
    compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta t lambda := by
  rcases hleft with
    ⟨containerLeft, containerRight, hlength, hcontain⟩
  have hleftRight : containerLeft <= containerRight := by
    have hsqrt : 0 <= Real.sqrt (lambda * delta / t) := Real.sqrt_nonneg _
    linarith
  let containerRectangle : GraphRectangle :=
    { graph := R.rectangle.graph
      left := containerLeft
      right := containerRight
      left_le_right := hleftRight }
  let container : C2GraphRectangle :=
    { rectangle := containerRectangle
      first := R.first
      second := R.second
      graph_hasDeriv := R.graph_hasDeriv
      first_hasDeriv := R.first_hasDeriv }
  refine ⟨container, ?_, ?_, ?_⟩
  · exact hlength
  · simpa [C2GraphRectangle.carrier, GraphRectangle.carrier,
      GraphRectangle.base, container, containerRectangle] using hcontain
  · intro z hz
    simpa [container, containerRectangle] using hR z hz

/-- The compact-C2 comparability graph induced by a rectangle-valued map. -/
def compactC2ComparableAt
    {alpha : Type u} (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    (delta t lambda : Real) (a b : alpha) : Prop :=
  compactC2SymmetricGraphLambdaComparableOn
    domain center (rectangleAt a) (rectangleAt b) delta t lambda

theorem compactC2ComparableAt_symm
    {alpha : Type u} {rectangleAt : alpha -> C2GraphRectangle}
    {domain : Set Real} {center : C2GraphRectangle}
    {delta t lambda : Real} :
    Std.Symm (compactC2ComparableAt rectangleAt domain center delta t lambda) := by
  constructor
  intro a b hab
  exact compactC2SymmetricGraphLambdaComparableOn_symm hab

/-- PYZ Lemma 3.16 with an explicit Lemma 3.12 boundary.

`hneighbourContainer` is precisely the geometric composition statement:
for one pivot, its closed `comparisonLambda`-neighbourhood fits in one
`packingLambda` rectangle from the same compact C2 ball.  Once supplied,
the repository's proved Lemma 3.15 automatically gives the neighbourhood
bound, and the generic greedy theorem gives one subfamily preserving both
cardinality and arbitrary `ENNReal` mass.
-/
theorem exists_greedy_compactC2_incomparable_of_neighbour_containers
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    {delta t comparisonLambda packingLambda : Real}
    (weight : alpha -> ENNReal)
    (hdelta : 0 < delta) (ht : 0 < t)
    (hpackingLambda : 100 <= packingLambda)
    (hlength : forall a, a ∈ vertices ->
      (rectangleAt a).rectangle.right -
          (rectangleAt a).rectangle.left = Real.sqrt (delta / t))
    (hbase : forall a, a ∈ vertices ->
      (rectangleAt a).rectangle.base ⊆ domain)
    (hball : forall a, a ∈ vertices ->
      InPointwiseC2BallOn domain center (rectangleAt a) (3 * t))
    (hHundredIncomparable : Set.Pairwise (vertices : Set alpha)
      (fun a b =>
        ¬ compactC2ComparableAt rectangleAt domain center delta t 100 a b))
    (hneighbourContainer : forall a, a ∈ vertices ->
      exists container : C2GraphRectangle,
        container.rectangle.right - container.rectangle.left =
          Real.sqrt (packingLambda * delta / t) ∧
        (forall b, b ∈ vertices ->
          (b = a ∨ compactC2ComparableAt rectangleAt domain center
              delta t comparisonLambda a b) ->
          (rectangleAt b).carrier delta ⊆
            container.carrier (packingLambda * delta)) ∧
        InPointwiseC2BallOn domain center container (3 * t)) :
    exists selected : Finset alpha,
      selected ⊆ vertices ∧
      (vertices.Nonempty -> selected.Nonempty) ∧
      Set.Pairwise (selected : Set alpha)
        (fun a b =>
          ¬ compactC2ComparableAt rectangleAt domain center
            delta t comparisonLambda a b) ∧
      (vertices.card : ENNReal) <=
        pyzClosedNeighbourBound packingLambda *
          (selected.card : ENNReal) ∧
      (∑ a ∈ vertices, weight a) <=
        pyzClosedNeighbourBound packingLambda *
          ∑ a ∈ selected, weight a := by
  classical
  apply exists_greedy_pairwise_not_relation vertices
    (compactC2ComparableAt rectangleAt domain center
      delta t comparisonLambda)
    compactC2ComparableAt_symm weight
    (pyzClosedNeighbourBound packingLambda)
  intro a ha
  obtain ⟨container, hcontainerLength, hcontain, hballContainer⟩ :=
    hneighbourContainer a ha
  let neighbour := vertices.filter (fun x =>
    x = a ∨ compactC2ComparableAt rectangleAt domain center
      delta t comparisonLambda a x)
  have hpacked :=
    card_le_of_pyz_rectangle_geometry_of_mem_common_c2BallOn
      neighbour rectangleAt container center domain hdelta ht
        hpackingLambda
      (fun i hi => hlength i (Finset.filter_subset _ _ hi))
      hcontainerLength
      (fun i hi =>
        have hiData := Finset.mem_filter.mp hi
        hcontain i hiData.1 hiData.2)
      (fun i hi => hbase i (Finset.filter_subset _ _ hi))
      (fun i hi => hball i (Finset.filter_subset _ _ hi))
      hballContainer
      (fun i hi j hj hij => by
        have hiVertices : i ∈ vertices := Finset.filter_subset _ _ hi
        have hjVertices : j ∈ vertices := Finset.filter_subset _ _ hj
        have hnotCompact :=
          hHundredIncomparable hiVertices hjVertices hij
        intro hleft
        exact hnotCompact
          (compactC2SymmetricGraphLambdaComparableOn_of_left
            (hball i hiVertices) hleft))
  simpa [neighbour, pyzClosedNeighbourBound] using hpacked

#print axioms pyzClosedNeighbourBound
#print axioms compactC2SymmetricGraphLambdaComparableOn_of_left
#print axioms compactC2ComparableAt
#print axioms compactC2ComparableAt_symm
#print axioms exists_greedy_compactC2_incomparable_of_neighbour_containers

end

end FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
