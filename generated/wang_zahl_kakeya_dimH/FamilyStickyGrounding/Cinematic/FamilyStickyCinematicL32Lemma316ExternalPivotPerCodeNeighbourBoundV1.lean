import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma315ExternalContainerSlopeFactorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped ENNReal Interval

namespace FamilyStickyCinematicL32Lemma316ExternalPivotPerCodeNeighbourBoundV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma315ExternalContainerSlopeFactorV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u

/-!
# External-pivot AtScales neighbour packing inside one local cover code

Fix an arbitrary pivot, possibly belonging to another cover code.  Inside
one target code the locally selected rectangles remain `100`-incomparable
and lie in one local `3*t` C2 ball.  Every target rectangle comparable to
the external pivot is contained in the pivot-centred two-scale dilation.

The target and pivot local centres may differ.  If both are within
`centerGap` in second derivative of one global centre, then a target
rectangle differs from the pivot dilation by at most
`6*t + 2*centerGap`.  The external-container slope-factor theorem therefore
gives an explicit per-code neighbour bound without assuming cross-code
Pairwise incomparability.
-/

/-- The slice of one target code lying in the external pivot's closed
AtScales neighbourhood. -/
noncomputable def externalPivotAtScalesNeighbourSlice
    {alpha : Type u} (target : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda : Real)
    (pivot : alpha) : Finset alpha := by
  classical
  exact target.filter fun b => b = pivot ∨
    compactC2ComparableAtScales rectangleAt domain globalCenter delta
      localScale referenceScale comparisonLambda pivot b

@[simp]
theorem mem_externalPivotAtScalesNeighbourSlice_iff
    {alpha : Type u} (target : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda : Real)
    (pivot b : alpha) :
    b ∈ externalPivotAtScalesNeighbourSlice target rectangleAt domain
      globalCenter delta localScale referenceScale comparisonLambda pivot <->
      b ∈ target ∧ (b = pivot ∨
        compactC2ComparableAtScales rectangleAt domain globalCenter delta
          localScale referenceScale comparisonLambda pivot b) := by
  classical
  simp [externalPivotAtScalesNeighbourSlice]

/-- Per-code closed-neighbour cap around an arbitrary external pivot.  The
slope-window arithmetic is deliberately a named input so a later numeric
adapter can choose `K` without division. -/
theorem externalPivotAtScalesNeighbourSlice_card_le
    {alpha : Type u} [DecidableEq alpha]
    (target : Finset alpha) (pivot : alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real)
    (targetLocalCenter pivotLocalCenter globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap K : Real}
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
    (hlength : forall b, b ∈ target ->
      (rectangleAt b).rectangle.right -
          (rectangleAt b).rectangle.left =
        Real.sqrt (delta / localScale))
    (hpivotLength :
      (rectangleAt pivot).rectangle.right -
          (rectangleAt pivot).rectangle.left =
        Real.sqrt (delta / localScale))
    (hbase : forall b, b ∈ target ->
      (rectangleAt b).rectangle.base ⊆ domain)
    (hpivotBase : (rectangleAt pivot).rectangle.base ⊆ domain)
    (hballTarget : forall b, b ∈ target ->
      InPointwiseC2BallOn domain targetLocalCenter
        (rectangleAt b) (3 * localScale))
    (htargetCenterSecond : forall z, z ∈ domain ->
      |targetLocalCenter.second z - globalCenter.second z| <= centerGap)
    (hballPivot : InPointwiseC2BallOn domain pivotLocalCenter
      (rectangleAt pivot) (3 * localScale))
    (hpivotCenterSecond : forall z, z ∈ domain ->
      |pivotLocalCenter.second z - globalCenter.second z| <= centerGap)
    (hsegmentDomain : forall b, b ∈ target ->
      forall x, x ∈ (rectangleAt pivot).rectangle.base ->
      forall y, y ∈ (rectangleAt b).rectangle.base ->
        [[x, y]] ⊆ domain)
    (hHundredIncomparable : Set.Pairwise (target : Set alpha)
      (fun a b =>
        ¬ compactC2ComparableAt rectangleAt domain targetLocalCenter
          delta localScale 100 a b)) :
    ((externalPivotAtScalesNeighbourSlice target rectangleAt domain
      globalCenter delta localScale referenceScale comparisonLambda
        pivot).card : ENNReal) <=
      pyzExternalContainerClosedNeighbourBound
        (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)
        K := by
  classical
  let packingLambda := pyzLemma312TwoScalePackingLambda
    comparisonLambda curvatureRatio
  let neighbour := externalPivotAtScalesNeighbourSlice target rectangleAt
    domain globalCenter delta localScale referenceScale comparisonLambda pivot
  let container := centeredC2GraphRectangleDilation
    (rectangleAt pivot) delta localScale packingLambda
  have hcomparisonOne : 1 <= comparisonLambda := by linarith
  have hpackingNonneg : 0 <= packingLambda :=
    pyzLemma312TwoScalePackingLambda_nonneg hcomparisonOne hratio
  have hpackingOne : 1 <= packingLambda := by
    have hpackingHundred : 100 <= packingLambda :=
      pyzLemma312TwoScalePackingLambda_ge_hundred
        hcomparisonLambda hratio
    linarith
  apply card_le_of_pyz_externalContainerSlopeFactor_on_bases
    neighbour rectangleAt container hdelta hlocal hpackingNonneg
      (show 0 <= 6 * localScale + 2 * centerGap by
        nlinarith [hlocal.le, hcenterGap])
      hK
  · intro b hb
    exact hlength b
      (mem_externalPivotAtScalesNeighbourSlice_iff target rectangleAt domain
        globalCenter delta localScale referenceScale comparisonLambda pivot b
          |>.mp hb |>.1)
  · exact centeredC2GraphRectangleDilation_length
      (rectangleAt pivot) delta localScale packingLambda
  · intro b hb
    have hbData :=
      (mem_externalPivotAtScalesNeighbourSlice_iff target rectangleAt domain
        globalCenter delta localScale referenceScale comparisonLambda pivot b
          |>.mp hb)
    rcases hbData.2 with hbpivot | hcomparable
    · subst b
      exact carrier_subset_centeredC2GraphRectangleDilation
        (rectangleAt pivot) hdelta.le hlocal hpackingOne hpivotLength
    · exact
        carrier_subset_centeredDilation_of_compactC2ComparableAtScales_twoCenter
          hdelta hlocal hcomparisonOne hratio hscaleRatio hpivotLength
          hpivotBase hballPivot hpivotCenterSecond
          (hsegmentDomain b hbData.1) hcomparable
  · intro i hi j hj hij z hz
    have hiTarget :=
      (mem_externalPivotAtScalesNeighbourSlice_iff target rectangleAt domain
        globalCenter delta localScale referenceScale comparisonLambda pivot i
          |>.mp hi |>.1)
    have hjTarget :=
      (mem_externalPivotAtScalesNeighbourSlice_iff target rectangleAt domain
        globalCenter delta localScale referenceScale comparisonLambda pivot j
          |>.mp hj |>.1)
    rcases hz with hzi | hzj
    · exact abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
        (hballTarget i hiTarget) (hballTarget j hjTarget)
          (hbase i hiTarget hzi)
    · exact abs_second_sub_le_six_mul_t_of_mem_common_c2BallOn
        (hballTarget i hiTarget) (hballTarget j hjTarget)
          (hbase j hjTarget hzj)
  · intro b hb z hz
    have hbTarget :=
      (mem_externalPivotAtScalesNeighbourSlice_iff target rectangleAt domain
        globalCenter delta localScale referenceScale comparisonLambda pivot b
          |>.mp hb |>.1)
    have hzDomain : z ∈ domain := hbase b hbTarget hz
    have hbGlobal :
        |(rectangleAt b).second z - globalCenter.second z| <=
          3 * localScale + centerGap := by
      calc
        |(rectangleAt b).second z - globalCenter.second z| <=
            |(rectangleAt b).second z - targetLocalCenter.second z| +
              |targetLocalCenter.second z - globalCenter.second z| :=
          abs_sub_le _ _ _
        _ <= 3 * localScale + centerGap :=
          add_le_add (hballTarget b hbTarget z hzDomain).2.2
            (htargetCenterSecond z hzDomain)
    have hpivotGlobal :
        |(rectangleAt pivot).second z - globalCenter.second z| <=
          3 * localScale + centerGap := by
      calc
        |(rectangleAt pivot).second z - globalCenter.second z| <=
            |(rectangleAt pivot).second z - pivotLocalCenter.second z| +
              |pivotLocalCenter.second z - globalCenter.second z| :=
          abs_sub_le _ _ _
        _ <= 3 * localScale + centerGap :=
          add_le_add (hballPivot z hzDomain).2.2
            (hpivotCenterSecond z hzDomain)
    change |(rectangleAt b).second z - (rectangleAt pivot).second z| <=
      6 * localScale + 2 * centerGap
    calc
      |(rectangleAt b).second z - (rectangleAt pivot).second z| <=
          |(rectangleAt b).second z - globalCenter.second z| +
            |globalCenter.second z - (rectangleAt pivot).second z| :=
        abs_sub_le _ _ _
      _ = |(rectangleAt b).second z - globalCenter.second z| +
          |(rectangleAt pivot).second z - globalCenter.second z| := by
        rw [abs_sub_comm (globalCenter.second z)
          ((rectangleAt pivot).second z)]
      _ <= (3 * localScale + centerGap) +
          (3 * localScale + centerGap) := add_le_add hbGlobal hpivotGlobal
      _ = 6 * localScale + 2 * centerGap := by ring
  · simpa only [packingLambda] using hslopeWindow
  · intro i hi j hj hij
    have hiTarget :=
      (mem_externalPivotAtScalesNeighbourSlice_iff target rectangleAt domain
        globalCenter delta localScale referenceScale comparisonLambda pivot i
          |>.mp hi |>.1)
    have hjTarget :=
      (mem_externalPivotAtScalesNeighbourSlice_iff target rectangleAt domain
        globalCenter delta localScale referenceScale comparisonLambda pivot j
          |>.mp hj |>.1)
    have hnotCompact := hHundredIncomparable hiTarget hjTarget hij
    intro hleft
    exact hnotCompact
      (compactC2SymmetricGraphLambdaComparableOn_of_left
        (hballTarget i hiTarget) hleft)

#print axioms externalPivotAtScalesNeighbourSlice_card_le

end

end FamilyStickyCinematicL32Lemma316ExternalPivotPerCodeNeighbourBoundV1
