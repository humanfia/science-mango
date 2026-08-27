import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresClosedNeighbourCodeSumV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316ExternalPivotPerCodeNeighbourBoundV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped ENNReal Interval

namespace FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteNestedValueFibresClosedNeighbourCodeSumV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma315ExternalContainerSlopeFactorV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma316ExternalPivotPerCodeNeighbourBoundV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u v

/-!
# External-pivot third-stage neighbour bound over local cover codes

This is the geometric consumer of the pure sigma code-sum lemma.  Inside
each target code it applies the external-container PYZ packing theorem;
then it sums those slices using the retained code tags.  It does not assume
cross-code incomparability or disjointness of underlying endpoint tubes.
-/

/-- Forget the local-cover code tag when assigning a rectangle to a
third-stage candidate. -/
def codeSelectedRectangleAt
    {code : Type v} {item : Type u}
    (rectangleAt : item -> C2GraphRectangle) :
    CodeSelectedCandidate code item -> C2GraphRectangle :=
  fun q => rectangleAt q.2

@[simp]
theorem codeSelectedRectangleAt_apply
    {code : Type v} {item : Type u}
    (rectangleAt : item -> C2GraphRectangle)
    (q : CodeSelectedCandidate code item) :
    codeSelectedRectangleAt rectangleAt q = rectangleAt q.2 := rfl

/-- Honest cross-code closed-neighbour estimate.  The only combinatorial
loss beyond the per-code PYZ cap is the external bound `codeBound` on the
number of occupied cover codes. -/
theorem codeSelectedCandidates_closedNeighbour_card_le_of_externalPivotPerCode
    {code : Type v} {item : Type u}
    [DecidableEq code] [DecidableEq item]
    (codes : Finset code) (selectedAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap K : Real}
    (codeBound : ENNReal)
    (hcodes : (codes.card : ENNReal) <= codeBound)
    (hdelta : 0 < delta) (hlocal : 0 < localScale)
    (hcomparisonLambda : 100 <= comparisonLambda)
    (hratio : 0 <= curvatureRatio)
    (hscaleRatio :
      3 * localScale + centerGap + 3 * referenceScale <=
        curvatureRatio * localScale)
    (hcenterGap : 0 <= centerGap)
    (hK : 0 <= K)
    (hslopeWindow :
      4 *
          (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio *
            delta) +
        2 * (6 * localScale + 2 * centerGap) *
            (Real.sqrt (delta / localScale)) ^ 2 <=
          (K * Real.sqrt (delta * localScale)) *
            (Real.sqrt (delta / localScale) / 2))
    (hlength : forall k, k ∈ codes -> forall b, b ∈ selectedAt k ->
      (rectangleAt b).rectangle.right -
          (rectangleAt b).rectangle.left =
        Real.sqrt (delta / localScale))
    (hbase : forall k, k ∈ codes -> forall b, b ∈ selectedAt k ->
      (rectangleAt b).rectangle.base ⊆ domain)
    (hball : forall k, k ∈ codes -> forall b, b ∈ selectedAt k ->
      InPointwiseC2BallOn domain (localCenterAt k)
        (rectangleAt b) (3 * localScale))
    (hcenterSecond : forall k, k ∈ codes -> forall z, z ∈ domain ->
      |(localCenterAt k).second z - globalCenter.second z| <= centerGap)
    (hsegmentDomain : forall kp, kp ∈ codes ->
      forall p, p ∈ selectedAt kp ->
      forall k, k ∈ codes -> forall b, b ∈ selectedAt k ->
      forall x, x ∈ (rectangleAt p).rectangle.base ->
      forall y, y ∈ (rectangleAt b).rectangle.base ->
        [[x, y]] ⊆ domain)
    (hHundredIncomparable : forall k, k ∈ codes ->
      Set.Pairwise (selectedAt k : Set item)
        (fun a b =>
          ¬ compactC2ComparableAt rectangleAt domain (localCenterAt k)
            delta localScale 100 a b))
    (q : CodeSelectedCandidate code item)
    (hq : q ∈ codeSelectedCandidates codes selectedAt) :
    ((finiteClosedComparableNeighbour
        (codeSelectedCandidates codes selectedAt)
        (compactC2ComparableAtScales (codeSelectedRectangleAt rectangleAt)
          domain globalCenter delta localScale referenceScale
            comparisonLambda) q).card : ENNReal) <=
      codeBound *
        pyzExternalContainerClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)
          K := by
  classical
  have hqData :=
    (mem_codeSelectedCandidates_iff codes selectedAt q).mp hq
  apply
    finiteClosedComparableNeighbour_codeSelectedCandidates_card_le_of_codeBound
      codes selectedAt
        (compactC2ComparableAtScales (codeSelectedRectangleAt rectangleAt)
          domain globalCenter delta localScale referenceScale
            comparisonLambda)
        q codeBound
        (pyzExternalContainerClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)
          K)
        hcodes
  intro k hk
  let itemSlice := externalPivotAtScalesNeighbourSlice (selectedAt k)
    rectangleAt domain globalCenter delta localScale referenceScale
      comparisonLambda q.2
  have hsliceSubset :
      finiteClosedComparableCodeSlice selectedAt
          (compactC2ComparableAtScales
            (codeSelectedRectangleAt rectangleAt) domain globalCenter delta
              localScale referenceScale comparisonLambda)
          q k ⊆ itemSlice := by
    intro b hb
    have hbData :=
      (mem_finiteClosedComparableCodeSlice_iff selectedAt
        (compactC2ComparableAtScales
          (codeSelectedRectangleAt rectangleAt) domain globalCenter delta
            localScale referenceScale comparisonLambda)
        q k b).mp hb
    apply (mem_externalPivotAtScalesNeighbourSlice_iff (selectedAt k)
      rectangleAt domain globalCenter delta localScale referenceScale
        comparisonLambda q.2 b).mpr
    refine ⟨hbData.1, ?_⟩
    rcases hbData.2 with heq | hcomparable
    · left
      exact congrArg
        (fun r : CodeSelectedCandidate code item => r.2) heq
    · right
      simpa only [compactC2ComparableAtScales, codeSelectedRectangleAt]
        using hcomparable
  have hsliceCardNat := Finset.card_le_card hsliceSubset
  have hsliceCard :
      ((finiteClosedComparableCodeSlice selectedAt
        (compactC2ComparableAtScales
          (codeSelectedRectangleAt rectangleAt) domain globalCenter delta
            localScale referenceScale comparisonLambda)
        q k).card : ENNReal) <= (itemSlice.card : ENNReal) := by
    exact_mod_cast hsliceCardNat
  refine hsliceCard.trans ?_
  exact externalPivotAtScalesNeighbourSlice_card_le
    (target := selectedAt k) (pivot := q.2)
    (rectangleAt := rectangleAt) (domain := domain)
    (targetLocalCenter := localCenterAt k)
    (pivotLocalCenter := localCenterAt q.1)
    (globalCenter := globalCenter)
    (hdelta := hdelta) (hlocal := hlocal)
    (hcomparisonLambda := hcomparisonLambda) (hratio := hratio)
    (hscaleRatio := hscaleRatio) (hcenterGap := hcenterGap)
    (hK := hK) (hslopeWindow := hslopeWindow)
    (hlength := hlength k hk)
    (hpivotLength := hlength q.1 hqData.1 q.2 hqData.2)
    (hbase := hbase k hk)
    (hpivotBase := hbase q.1 hqData.1 q.2 hqData.2)
    (hballTarget := hball k hk)
    (htargetCenterSecond := hcenterSecond k hk)
    (hballPivot := hball q.1 hqData.1 q.2 hqData.2)
    (hpivotCenterSecond := hcenterSecond q.1 hqData.1)
    (hsegmentDomain := fun b hb x hx y hy =>
      hsegmentDomain q.1 hqData.1 q.2 hqData.2 k hk b hb x hx y hy)
    (hHundredIncomparable := hHundredIncomparable k hk)

#print axioms codeSelectedCandidates_closedNeighbour_card_le_of_externalPivotPerCode

end

end FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
