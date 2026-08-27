import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonMidpointRootConsumerGlobalOnItemsCleanV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonOpenSupportSeparationTwoScaleRepoV2V1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonMidpointRootConsumerTwoScaleRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32GlobalTraceRootEncCardCleanV2
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonArcExactRootsOnItemsCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonMidpointRootConsumerGlobalOnItemsCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonOpenSupportSeparationTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalMoonOpenSupportSeparationCoreCleanV1
open FamilyStickyCinematicL32Prop41RankedIntervalSamplesV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

private theorem strict_opposite_of_interval_sign_and_exact_endpointsAtScales
    {left right theta hostValue neighborValue : Real}
    (hleftRight : left < right)
    (hout : theta < left ∨ right < theta)
    (hsign : theta ∈ Ioo left right <-> neighborValue < hostValue)
    (hroot : hostValue = neighborValue <->
      theta = left ∨ theta = right) :
    hostValue < neighborValue := by
  have hnotInside : theta ∉ Ioo left right := by
    intro hmem
    rcases hout with hout | hout <;> linarith [hmem.1, hmem.2]
  have hnotNeighborLt : ¬ neighborValue < hostValue := by
    intro hlt
    exact hnotInside (hsign.mpr hlt)
  have hle : hostValue <= neighborValue := le_of_not_gt hnotNeighborLt
  have hne : hostValue ≠ neighborValue := by
    intro heq
    rcases hroot.mp heq with hleft | hright
    · rcases hout with hout | hout <;> linarith [hleftRight]
    · rcases hout with hout | hout <;> linarith [hleftRight]
  exact lt_of_le_of_ne hle hne

/-- All midpoint signs and root-cardinality inputs for the K23 obstruction,
with an independent common-reference C2 scale. -/
theorem pairLocalActualMoon_midpointRootDataAtScales_global_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p,
        pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 f2 : Real -> Real) (A B M : Real)
    (depth : FirstGenerationCurve curves -> Real)
    (center : C2GraphRectangle) {domain : Set Real}
    {delta localScale referenceScale lambda0 lambda : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta localScale lambda0)
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems
        curves items T U hT hU hpair rectangles f f1 A B M depth D)
      items leftHost rightHost x y z)
    (hAB : A < B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hcommonC : forall V, V ∈ curves -> forall W, W ∈ curves ->
      tubeGraphC V = tubeGraphC W)
    (hcoefficient : forall V, V ∈ curves -> forall W, W ∈ curves ->
      V ≠ W -> 0 < tubePairCoefficientDistance V W)
    (hfDeriv : forall theta, HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, HasDerivAt f1 (f2 theta) theta)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda0) * delta <
      localScale / 1200)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hendpoint : EndpointValuesDistinct curves
      (fun V => actualTubeGraph V f) A B)
    (hA3 : NoTangentialGraphIntersections curves
      (fun V => actualTubeGraph V f)
      (fun V => actualTubeGraphFirst V f f1) A B)
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta localScale <=
      Real.sqrt (lambda * delta / localScale))
    (hreference : forall V, V ∈ curves ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB.le)
        (3 * referenceScale))
    (hpairwise : Set.Pairwise
      (items : Set (FirstGenerationCurvePair curves))
      (fun p q => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (rectangles p) (rectangles q)
          delta localScale referenceScale lambda))) :
    let P := pairLocalActualMoonOpenSupportDataAtScales_global_onItems
      curves items T U hT hU hpair rectangles f f1 f2 A B M depth center D C
      hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hendpoint hA3 henlarge hscale hreference hpairwise
    PairLocalMoonMidpointRootData P.innerSeparatedIntervals
      P.hostGraph P.neighborGraph A B := by
  let P := pairLocalActualMoonOpenSupportDataAtScales_global_onItems
    curves items T U hT hU hpair rectangles f f1 f2 A B M depth center D C
    hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
    hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
    hendpoint hA3 henlarge hscale hreference hpairwise
  let S := P.innerSeparatedIntervals
  refine {
    own := ?_
    foreign := ?_
    midpoint_mem := P.intervalMidpoint_inner_mem_Icc
    host_continuous := ?_
    neighbor_continuous := ?_
    host_root_encard_le_two := ?_
    neighbor_root_encard_le_two := ?_ }
  · intro e
    exact (P.positive_iff e (intervalMidpoint S e)
      (P.intervalMidpoint_inner_mem_Icc e)).mp
        (P.intervalMidpoint_inner_mem_original_Ioo e)
  · intro e q heq
    have hthetaAB := P.intervalMidpoint_inner_mem_Icc e
    have hout : intervalMidpoint S e < P.left q ∨
        P.right q < intervalMidpoint S e := by
      rcases P.pair_ordered_le heq with hbefore | hafter
      · exact Or.inl <| (P.intervalMidpoint_inner_mem_original_Ioo e).2.trans_le
          hbefore
      · exact Or.inr <| hafter.trans_lt
          (P.intervalMidpoint_inner_mem_original_Ioo e).1
    exact strict_opposite_of_interval_sign_and_exact_endpointsAtScales
      (P.left_lt_right q) hout
      (P.positive_iff q (intervalMidpoint S e) hthetaAB)
      (pairLocalActualMoonArc_graph_eq_iff_endpoint_onItems
        curves items T U hT hU hpair rectangles f f1 A B M depth D
        (moonSixArc C q.1 q.2) hthetaAB)
  · intro h theta _
    exact (hasDerivAt_actualTubeGraph (moonHost C h).1
      (hfDeriv theta)).continuousAt.continuousWithinAt
  · intro j theta _
    exact (hasDerivAt_actualTubeGraph (moonNeighbor C j).1
      (hfDeriv theta)).continuousAt.continuousWithinAt
  · intro h0 h1 hh
    have hraw : (moonHost C h0).1 ≠ (moonHost C h1).1 := by
      intro heq
      exact hh ((moonHost_injective C) (Subtype.ext heq))
    simpa only [P, pairLocalActualMoonOpenSupportDataAtScales_global_onItems,
      actualTubeGraph, cinematicTraceValue, skirtTubeGraphA, skirtTubeGraphB,
      skirtTubeGraphC, skirtTubeGraphD, tubeGraphA, tubeGraphB, tubeGraphC,
      tubeGraphD] using
      (tubeCinematicTrace_pair_rootSet_encard_le_two_global
        (moonHost C h0).1 (moonHost C h1).1 f f1 f2 hAB.le
        (hcommonC _ (moonHost C h0).2 _ (moonHost C h1).2)
        (hcoefficient _ (moonHost C h0).2 _ (moonHost C h1).2 hraw)
        hparameter hft hf1Lower hf1Upper hf2
        (fun theta _ => hfDeriv theta)
        (fun theta _ => hf1Deriv theta))
  · intro j0 j1 hj
    have hraw : (moonNeighbor C j0).1 ≠ (moonNeighbor C j1).1 := by
      intro heq
      exact hj ((moonNeighbor_injective C) (Subtype.ext heq))
    simpa only [P, pairLocalActualMoonOpenSupportDataAtScales_global_onItems,
      actualTubeGraph, cinematicTraceValue, skirtTubeGraphA, skirtTubeGraphB,
      skirtTubeGraphC, skirtTubeGraphD, tubeGraphA, tubeGraphB, tubeGraphC,
      tubeGraphD] using
      (tubeCinematicTrace_pair_rootSet_encard_le_two_global
        (moonNeighbor C j0).1 (moonNeighbor C j1).1 f f1 f2 hAB.le
        (hcommonC _ (moonNeighbor C j0).2 _ (moonNeighbor C j1).2)
        (hcoefficient _ (moonNeighbor C j0).2 _ (moonNeighbor C j1).2 hraw)
        hparameter hft hf1Lower hf1Upper hf2
        (fun theta _ => hfDeriv theta)
        (fun theta _ => hf1Deriv theta))

#print axioms pairLocalActualMoon_midpointRootDataAtScales_global_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonMidpointRootConsumerTwoScaleRepoV2V1
