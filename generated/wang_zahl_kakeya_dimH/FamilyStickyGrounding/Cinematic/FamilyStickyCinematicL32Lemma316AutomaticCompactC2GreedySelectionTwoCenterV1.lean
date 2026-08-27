import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Lemma55SymmetricRectangleComparabilityV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
open FamilyStickyCinematicL32Prop41TwoScaleComparabilityCoreV1

noncomputable section

universe u

/-- The compact two-scale comparison graph induced by a rectangle map. -/
def compactC2ComparableAtScales
    {alpha : Type u} (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    (delta localScale referenceScale lambda : Real) (a b : alpha) : Prop :=
  compactC2SymmetricGraphLambdaComparableOnAtScales
    domain center (rectangleAt a) (rectangleAt b)
      delta localScale referenceScale lambda

theorem compactC2ComparableAtScales_symm
    {alpha : Type u} {rectangleAt : alpha -> C2GraphRectangle}
    {domain : Set Real} {center : C2GraphRectangle}
    {delta localScale referenceScale lambda : Real} :
    Std.Symm (compactC2ComparableAtScales rectangleAt domain center
      delta localScale referenceScale lambda) := by
  constructor
  intro a b hab
  exact compactC2SymmetricGraphLambdaComparableOnAtScales_symm hab

/-!
The greedy relation remains based at `globalCenter`, but the finite
rectangles may lie in a different local C2 ball.  The only connection between
the two centres is an explicit second-derivative bridge.
-/

theorem exists_greedy_compactC2_incomparable_automaticAtScales_twoCenter
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (localCenter globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap : Real}
    (weight : alpha -> ENNReal)
    (hdelta : 0 < delta) (hlocal : 0 < localScale)
    (hcomparisonLambda : 100 <= comparisonLambda)
    (hratio : 0 <= curvatureRatio)
    (hscaleRatio :
      3 * localScale + centerGap + 3 * referenceScale <=
        curvatureRatio * localScale)
    (hlength : forall a, a ∈ vertices ->
      (rectangleAt a).rectangle.right -
          (rectangleAt a).rectangle.left =
        Real.sqrt (delta / localScale))
    (hbase : forall a, a ∈ vertices ->
      (rectangleAt a).rectangle.base ⊆ domain)
    (hballLocal : forall a, a ∈ vertices ->
      InPointwiseC2BallOn domain localCenter
        (rectangleAt a) (3 * localScale))
    (hcenterSecond : forall z, z ∈ domain ->
      |localCenter.second z - globalCenter.second z| <= centerGap)
    (hsegmentDomain : forall a, a ∈ vertices ->
      forall b, b ∈ vertices ->
      forall x, x ∈ (rectangleAt a).rectangle.base ->
      forall y, y ∈ (rectangleAt b).rectangle.base ->
        [[x, y]] ⊆ domain)
    (hHundredIncomparable : Set.Pairwise (vertices : Set alpha)
      (fun a b =>
        ¬ symmetricGraphLambdaComparable
          (rectangleAt a).rectangle (rectangleAt b).rectangle
            delta localScale 100)) :
    exists selected : Finset alpha,
      selected ⊆ vertices ∧
      (vertices.Nonempty -> selected.Nonempty) ∧
      Set.Pairwise (selected : Set alpha)
        (fun a b =>
          ¬ compactC2ComparableAtScales rectangleAt domain globalCenter
            delta localScale referenceScale comparisonLambda a b) ∧
      (vertices.card : ENNReal) <=
        pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          (selected.card : ENNReal) ∧
      (∑ a ∈ vertices, weight a) <=
        pyzClosedNeighbourBound
            (pyzLemma312TwoScalePackingLambda
              comparisonLambda curvatureRatio) *
          ∑ a ∈ selected, weight a := by
  classical
  let packingLambda := pyzLemma312TwoScalePackingLambda
    comparisonLambda curvatureRatio
  have hcomparisonOne : 1 <= comparisonLambda := by linarith
  have hpackingHundred : 100 <= packingLambda := by
    exact pyzLemma312TwoScalePackingLambda_ge_hundred
      hcomparisonLambda hratio
  have hpackingOne : 1 <= packingLambda := by linarith
  apply exists_greedy_pairwise_not_relation vertices
    (compactC2ComparableAtScales rectangleAt domain globalCenter delta localScale
      referenceScale comparisonLambda)
    compactC2ComparableAtScales_symm weight
    (pyzClosedNeighbourBound packingLambda)
  intro a ha
  let neighbour := vertices.filter (fun b =>
    b = a ∨ compactC2ComparableAtScales rectangleAt domain globalCenter
      delta localScale referenceScale comparisonLambda a b)
  let container := centeredC2GraphRectangleDilation
    (rectangleAt a) delta localScale packingLambda
  have hpacked :=
    card_le_of_pyz_rectangle_geometry_of_mem_common_c2BallOn
      neighbour rectangleAt container localCenter domain hdelta hlocal
        hpackingHundred
      (fun i hi => hlength i (Finset.filter_subset _ _ hi))
      (centeredC2GraphRectangleDilation_length
        (rectangleAt a) delta localScale packingLambda)
      (fun b hb => by
        have hbData := Finset.mem_filter.mp hb
        rcases hbData.2 with hba | hcomparable
        · subst b
          exact carrier_subset_centeredC2GraphRectangleDilation
            (rectangleAt a) hdelta.le hlocal hpackingOne (hlength a ha)
        · exact
            carrier_subset_centeredDilation_of_compactC2ComparableAtScales_twoCenter
              hdelta hlocal hcomparisonOne hratio hscaleRatio
              (hlength a ha) (hbase a ha) (hballLocal a ha)
              hcenterSecond (hsegmentDomain a ha b hbData.1) hcomparable)
      (fun i hi => hbase i (Finset.filter_subset _ _ hi))
      (fun i hi => hballLocal i (Finset.filter_subset _ _ hi))
      (centeredC2GraphRectangleDilation_mem_c2BallOn (hballLocal a ha))
      (fun i hi j hj hij => by
        have hiVertices : i ∈ vertices := Finset.filter_subset _ _ hi
        have hjVertices : j ∈ vertices := Finset.filter_subset _ _ hj
        have hnotSymmetric :=
          hHundredIncomparable hiVertices hjVertices hij
        exact not_left_of_not_symmetricGraphLambdaComparable hnotSymmetric)
  simpa [neighbour, packingLambda, pyzClosedNeighbourBound] using hpacked

#print axioms compactC2ComparableAtScales
#print axioms compactC2ComparableAtScales_symm
#print axioms exists_greedy_compactC2_incomparable_automaticAtScales_twoCenter

end

end FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
