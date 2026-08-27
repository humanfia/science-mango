import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma315ExternalContainerCurvatureRatioNumericsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped ENNReal Interval

namespace FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotCurvatureThirdStageV1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma315ExternalContainerCurvatureRatioNumericsV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u v

/-!
# Division-free third-stage outcome over local cover codes

The external second-derivative gap is encoded by the scale-free inequality

`6 * localScale + 2 * centerGap <= 2 * externalRatio * localScale`.

The numeric adapter then chooses the slope factor automatically.  The
resulting record is the reusable package-free interface expected from an
actual shifted-grid/local-cover specialization.
-/

/-- All finite and geometric inputs needed for the code-local external-pivot
count and the global third-stage greedy selection. -/
structure FiniteExternalPivotPerCodeCurvatureData
    {code : Type v} {item : Type u}
    [DecidableEq code] [DecidableEq item]
    (codes : Finset code) (selectedAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real)
    (codeBound : ENNReal) : Prop where
  codes_card : (codes.card : ENNReal) <= codeBound
  delta_pos : 0 < delta
  localScale_pos : 0 < localScale
  comparisonLambda_ge : 100 <= comparisonLambda
  curvatureRatio_nonneg : 0 <= curvatureRatio
  scale_ratio :
    3 * localScale + centerGap + 3 * referenceScale <=
      curvatureRatio * localScale
  centerGap_nonneg : 0 <= centerGap
  externalRatio_nonneg : 0 <= externalRatio
  external_gap :
    6 * localScale + 2 * centerGap <=
      2 * externalRatio * localScale
  length : forall k, k ∈ codes -> forall b, b ∈ selectedAt k ->
    (rectangleAt b).rectangle.right -
        (rectangleAt b).rectangle.left =
      Real.sqrt (delta / localScale)
  base : forall k, k ∈ codes -> forall b, b ∈ selectedAt k ->
    (rectangleAt b).rectangle.base ⊆ domain
  local_ball : forall k, k ∈ codes -> forall b, b ∈ selectedAt k ->
    InPointwiseC2BallOn domain (localCenterAt k)
      (rectangleAt b) (3 * localScale)
  center_second : forall k, k ∈ codes -> forall z, z ∈ domain ->
    |(localCenterAt k).second z - globalCenter.second z| <= centerGap
  segment_domain : forall kp, kp ∈ codes ->
    forall p, p ∈ selectedAt kp ->
    forall k, k ∈ codes -> forall b, b ∈ selectedAt k ->
    forall x, x ∈ (rectangleAt p).rectangle.base ->
    forall y, y ∈ (rectangleAt b).rectangle.base ->
      [[x, y]] ⊆ domain
  hundred_incomparable : forall k, k ∈ codes ->
    Set.Pairwise (selectedAt k : Set item)
      (fun a b =>
        ¬ compactC2ComparableAt rectangleAt domain (localCenterAt k)
          delta localScale 100 a b)

/-- The callback-free global closed-neighbour cap obtained from the data
package. -/
theorem codeSelectedCandidates_closedNeighbour_card_le_curvatureCap
    {code : Type v} {item : Type u}
    [DecidableEq code] [DecidableEq item]
    (codes : Finset code) (selectedAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal)
    (G : FiniteExternalPivotPerCodeCurvatureData codes selectedAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound)
    (q : CodeSelectedCandidate code item)
    (hq : q ∈ codeSelectedCandidates codes selectedAt) :
    ((finiteClosedComparableNeighbour
        (codeSelectedCandidates codes selectedAt)
        (compactC2ComparableAtScales (codeSelectedRectangleAt rectangleAt)
          domain globalCenter delta localScale referenceScale
            comparisonLambda) q).card : ENNReal) <=
      codeBound *
        pyzExternalContainerCurvatureClosedNeighbourCap
          (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)
          externalRatio := by
  let packingLambda := pyzLemma312TwoScalePackingLambda
    comparisonLambda curvatureRatio
  have hcomparisonOne : 1 <= comparisonLambda := by
    linarith [G.comparisonLambda_ge]
  have hpackingNonneg : 0 <= packingLambda :=
    pyzLemma312TwoScalePackingLambda_nonneg hcomparisonOne
      G.curvatureRatio_nonneg
  have hraw :=
    codeSelectedCandidates_closedNeighbour_card_le_of_externalPivotPerCode
      codes selectedAt rectangleAt domain localCenterAt globalCenter codeBound
      G.codes_card G.delta_pos G.localScale_pos G.comparisonLambda_ge
      G.curvatureRatio_nonneg G.scale_ratio G.centerGap_nonneg
      (pyzExternalContainerCurvatureSlopeFactor_nonneg hpackingNonneg
        G.externalRatio_nonneg)
      (externalContainerCurvatureRatio_slopeWindow G.delta_pos
        G.localScale_pos G.external_gap)
      G.length G.base G.local_ball G.center_second G.segment_domain
      G.hundred_incomparable q hq
  simpa only [packingLambda,
    pyzExternalContainerClosedNeighbourBound_at_curvatureSlopeFactor] using
      hraw

/-- A single common-C third-stage AtScales Pairwise family, with both the
per-code PYZ count and the occupied-code loss generated automatically. -/
theorem exists_codeSelectedCandidates_compactC2AtScalesThirdStageOutcome
    {code : Type v} {item : Type u}
    [DecidableEq code] [DecidableEq item]
    (codes : Finset code) (selectedAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal)
    (weight : CodeSelectedCandidate code item -> ENNReal)
    (G : FiniteExternalPivotPerCodeCurvatureData codes selectedAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound) :
    Nonempty (CompactC2AtScalesThirdStageOutcome
      (codeSelectedCandidates codes selectedAt)
      (codeSelectedRectangleAt rectangleAt) domain globalCenter delta
        localScale referenceScale comparisonLambda weight
        (codeBound *
          pyzExternalContainerCurvatureClosedNeighbourCap
            (pyzLemma312TwoScalePackingLambda comparisonLambda
              curvatureRatio)
            externalRatio)) := by
  classical
  apply exists_compactC2AtScalesThirdStageOutcome_of_closedNeighbourBound
  intro q hq
  exact codeSelectedCandidates_closedNeighbour_card_le_curvatureCap
    codes selectedAt rectangleAt domain localCenterAt globalCenter codeBound
      G q hq

#print axioms codeSelectedCandidates_closedNeighbour_card_le_curvatureCap
#print axioms exists_codeSelectedCandidates_compactC2AtScalesThirdStageOutcome

end

end FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotCurvatureThirdStageV1
