import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotCurvatureThirdStageV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped BigOperators ENNReal Interval

namespace FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1

open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotThirdStageV1
open FamilyStickyCinematicL32FiniteNestedValueFibresExternalPivotCurvatureThirdStageV1
open FamilyStickyCinematicL32Lemma312PivotCenteredContainerTwoCenterV1
open FamilyStickyCinematicL32Lemma315ExternalContainerCurvatureRatioNumericsV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Lemma316CompactC2GreedySelectionV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterV1
open FamilyStickyCinematicL32Lemma55Lemma316TwoStageGreedyClusteringAtScalesTwoCenterLocalCompactV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1

noncomputable section

universe u v

/-!
# Finite choice of local-compact outcomes over occupied cover codes

The code type is intended to be the subtype of a fixed common-C occupied
code finset.  Consequently `Finset.univ` is exactly the occupied code set,
and every code carries its occupancy proof.  This avoids choosing dummy
outcomes or geometric data for unoccupied codes.
-/

/-- Geometry and numerics on every occupied code fibre before either greedy
stage is run. -/
structure FiniteOccupiedCodeLocalCompactCurvatureData
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    (delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real)
    (codeBound : ENNReal) : Prop where
  code_card : (Fintype.card code : ENNReal) <= codeBound
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
  length : forall k, forall b, b ∈ rawAt k ->
    (rectangleAt b).rectangle.right -
        (rectangleAt b).rectangle.left =
      Real.sqrt (delta / localScale)
  base : forall k, forall b, b ∈ rawAt k ->
    (rectangleAt b).rectangle.base ⊆ domain
  local_ball : forall k, forall b, b ∈ rawAt k ->
    InPointwiseC2BallOn domain (localCenterAt k)
      (rectangleAt b) (3 * localScale)
  center_second : forall k, forall z, z ∈ domain ->
    |(localCenterAt k).second z - globalCenter.second z| <= centerGap
  segment_domain : forall kp, forall p, p ∈ rawAt kp ->
    forall k, forall b, b ∈ rawAt k ->
    forall x, x ∈ (rectangleAt p).rectangle.base ->
    forall y, y ∈ (rectangleAt b).rectangle.base ->
      [[x, y]] ⊆ domain

/-- Canonical finite choice of the local two-stage outcome at one occupied
code. -/
noncomputable def finiteOccupiedCodeLocalCompactOutcome
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound)
    (k : code) :
    CompactC2TwoStageAtScalesTwoCenterLocalCompactOutcome
      (rawAt k) rectangleAt domain (localCenterAt k) globalCenter delta
        localScale referenceScale comparisonLambda curvatureRatio centerGap
        (weightAt k) :=
  Classical.choice
    (exists_compactC2_twoStage_greedy_clusteringAtScales_twoCenter_localCompact
      (rawAt k) rectangleAt domain (localCenterAt k) globalCenter
      (weightAt k) G.delta_pos G.localScale_pos G.comparisonLambda_ge
      G.curvatureRatio_nonneg G.scale_ratio (G.length k) (G.base k)
      (G.local_ball k) (G.center_second k)
      (fun a ha b hb => G.segment_domain k a ha k b hb))

/-- The local selected pivots that become code-tagged third-stage
candidates. -/
noncomputable def finiteOccupiedCodeLocalCompactSelectedAt
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound) :
    code -> Finset item :=
  fun k => (finiteOccupiedCodeLocalCompactOutcome rawAt rectangleAt domain
    localCenterAt globalCenter codeBound weightAt G k).selected

/-- Owner-cluster mass attached to a local selected pivot. -/
noncomputable def finiteOccupiedCodeLocalCompactClusterWeightAt
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound) :
    code -> item -> ENNReal :=
  fun k => ownerClusterMass (rawAt k)
    (finiteOccupiedCodeLocalCompactOutcome rawAt rectangleAt domain
      localCenterAt globalCenter codeBound weightAt G k).owner
    (weightAt k)

theorem finiteOccupiedCodeLocalCompactSelectedAt_subset
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound)
    (k : code) :
    finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt domain
      localCenterAt globalCenter codeBound weightAt G k ⊆ rawAt k := by
  intro a ha
  exact
    (finiteOccupiedCodeLocalCompactOutcome rawAt rectangleAt domain
      localCenterAt globalCenter codeBound weightAt G k).pivots_subset
      ((finiteOccupiedCodeLocalCompactOutcome rawAt rectangleAt domain
        localCenterAt globalCenter codeBound weightAt G k).selected_subset_pivots ha)

/-- The first two stages' exact owner-mass loss at one code. -/
theorem finiteOccupiedCodeLocalCompact_rawMass_le_selectedClusterMass
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound)
    (k : code) :
    (∑ a ∈ rawAt k, weightAt k a) <=
      pyzClosedNeighbourBound
          (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio) *
        ∑ a ∈ finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt
          domain localCenterAt globalCenter codeBound weightAt G k,
          finiteOccupiedCodeLocalCompactClusterWeightAt rawAt rectangleAt
            domain localCenterAt globalCenter codeBound weightAt G k a := by
  exact
    (finiteOccupiedCodeLocalCompactOutcome rawAt rectangleAt domain
      localCenterAt globalCenter codeBound weightAt G k).raw_mass_le_selected_cluster_mass

/-- The selected local outcomes automatically satisfy every geometric
field required by the external-pivot code-sum theorem. -/
theorem finiteOccupiedCodeLocalCompactExternalPivotData
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound) :
    FiniteExternalPivotPerCodeCurvatureData
      (Finset.univ : Finset code)
      (finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt domain
        localCenterAt globalCenter codeBound weightAt G)
      rectangleAt domain localCenterAt globalCenter delta localScale
        referenceScale comparisonLambda curvatureRatio centerGap
          externalRatio codeBound := by
  let selectedAt := finiteOccupiedCodeLocalCompactSelectedAt rawAt
    rectangleAt domain localCenterAt globalCenter codeBound weightAt G
  let outcomeAt := finiteOccupiedCodeLocalCompactOutcome rawAt rectangleAt
    domain localCenterAt globalCenter codeBound weightAt G
  have hsubset : forall k, selectedAt k ⊆ rawAt k := by
    intro k
    exact finiteOccupiedCodeLocalCompactSelectedAt_subset rawAt rectangleAt
      domain localCenterAt globalCenter codeBound weightAt G k
  refine {
    codes_card := ?_
    delta_pos := G.delta_pos
    localScale_pos := G.localScale_pos
    comparisonLambda_ge := G.comparisonLambda_ge
    curvatureRatio_nonneg := G.curvatureRatio_nonneg
    scale_ratio := G.scale_ratio
    centerGap_nonneg := G.centerGap_nonneg
    externalRatio_nonneg := G.externalRatio_nonneg
    external_gap := G.external_gap
    length := ?_
    base := ?_
    local_ball := ?_
    center_second := ?_
    segment_domain := ?_
    hundred_incomparable := ?_ }
  · simpa only [Finset.card_univ] using G.code_card
  · intro k _hk b hb
    exact G.length k b (hsubset k hb)
  · intro k _hk b hb
    exact G.base k b (hsubset k hb)
  · intro k _hk b hb
    exact G.local_ball k b (hsubset k hb)
  · intro k _hk
    exact G.center_second k
  · intro kp _hkp p hp k _hk b hb
    exact G.segment_domain kp p (hsubset kp hp) k b (hsubset k hb)
  · intro k _hk a ha b hb hab
    exact (outcomeAt k).pivots_pairwise_hundred_local
      ((outcomeAt k).selected_subset_pivots ha)
      ((outcomeAt k).selected_subset_pivots hb) hab

/-- Fully automatic three-stage selected family over all occupied codes.
No local-outcome choice, Pairwise callback, global closed-neighbour callback,
or scalar slope-window callback remains. -/
theorem exists_finiteOccupiedCodeLocalCompactThirdStageOutcome
    {code : Type v} {item : Type u}
    [Fintype code] [DecidableEq code] [DecidableEq item]
    (rawAt : code -> Finset item)
    (rectangleAt : item -> C2GraphRectangle)
    (domain : Set Real)
    (localCenterAt : code -> C2GraphRectangle)
    (globalCenter : C2GraphRectangle)
    {delta localScale referenceScale comparisonLambda curvatureRatio
      centerGap externalRatio : Real}
    (codeBound : ENNReal) (weightAt : code -> item -> ENNReal)
    (G : FiniteOccupiedCodeLocalCompactCurvatureData rawAt rectangleAt
      domain localCenterAt globalCenter delta localScale referenceScale
        comparisonLambda curvatureRatio centerGap externalRatio codeBound) :
    Nonempty (CompactC2AtScalesThirdStageOutcome
      (codeSelectedCandidates (Finset.univ : Finset code)
        (finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt domain
          localCenterAt globalCenter codeBound weightAt G))
      (codeSelectedRectangleAt rectangleAt) domain globalCenter delta
        localScale referenceScale comparisonLambda
      (codeSelectedCandidateWeight
        (finiteOccupiedCodeLocalCompactClusterWeightAt rawAt rectangleAt
          domain localCenterAt globalCenter codeBound weightAt G))
      (codeBound *
        pyzExternalContainerCurvatureClosedNeighbourCap
          (pyzLemma312TwoScalePackingLambda comparisonLambda curvatureRatio)
          externalRatio)) := by
  classical
  exact exists_codeSelectedCandidates_compactC2AtScalesThirdStageOutcome
    (Finset.univ : Finset code)
    (finiteOccupiedCodeLocalCompactSelectedAt rawAt rectangleAt domain
      localCenterAt globalCenter codeBound weightAt G)
    rectangleAt domain localCenterAt globalCenter codeBound
    (codeSelectedCandidateWeight
      (finiteOccupiedCodeLocalCompactClusterWeightAt rawAt rectangleAt domain
        localCenterAt globalCenter codeBound weightAt G))
    (finiteOccupiedCodeLocalCompactExternalPivotData rawAt rectangleAt domain
      localCenterAt globalCenter codeBound weightAt G)

#print axioms finiteOccupiedCodeLocalCompactOutcome
#print axioms finiteOccupiedCodeLocalCompact_rawMass_le_selectedClusterMass
#print axioms finiteOccupiedCodeLocalCompactExternalPivotData
#print axioms exists_finiteOccupiedCodeLocalCompactThirdStageOutcome

end

end FamilyStickyCinematicL32FiniteOccupiedCodeLocalCompactThirdStageV1
