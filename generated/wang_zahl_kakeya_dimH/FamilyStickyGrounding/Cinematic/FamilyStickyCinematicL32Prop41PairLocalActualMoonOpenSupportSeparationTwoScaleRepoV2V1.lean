import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonPositiveSideSignOnItemsV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonSharedCurveOpenSupportDisjointGlobalCleanV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonSixBoundaryNonOverlapTwoScaleRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalMoonOpenSupportSeparationCoreCleanV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonOpenSupportSeparationTwoScaleRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonPositiveSideSignOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonSharedCurveOpenSupportDisjointGlobalCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonSixBoundaryNonOverlapTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalMoonOpenSupportSeparationCoreCleanV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- The six-support data with local lens scale and independent common-C2
reference scale. -/
def pairLocalActualMoonOpenSupportDataAtScales_global_onItems
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
    PairLocalMoonOpenSupportData where
  A := A
  B := B
  left e := (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaLeft
  right e := (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaRight
  left_mem e :=
    (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaLeft_mem
  right_mem e :=
    (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaRight_mem
  left_lt_right e :=
    (D (moonSixPair C e) (moonSixPair_mem_items C e)).theta_order
  hostGraph h := actualTubeGraph (moonHost C h).1 f
  neighborGraph j := actualTubeGraph (moonNeighbor C j).1 f
  positive_iff e theta htheta :=
    pairLocalActualMoonPositiveSide_mem_iff_neighbor_lt_host_onItems
      curves items T U hT hU hpair rectangles f f1 hAB M depth D
      hendpoint hA3 hfDeriv (moonSixArc C e.1 e.2) htheta
  sameHost_disjoint h := by
    intro j k hjk
    let arcE := moonSixArc C h j
    let arcQ := moonSixArc C h k
    have heq : (h, j) ≠ (h, k) := by
      intro heq
      exact hjk (congrArg Prod.snd heq)
    have hnot :=
      pairLocalActualMoonSixPairs_not_sharePositiveSegmentAtScales_global_onItems
        C curves T U hT hU rectangles f f1 f2 center hAB.le hdelta ht
        hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
        hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
        D henlarge hscale hreference hpairwise heq
    exact pairLocalActualMoon_sameHost_openSupports_disjoint_onItems
      curves items T U hT hU hpair rectangles f f1 A B M depth D
      arcE arcQ hnot
  sameNeighbor_disjoint j := by
    intro h k hhk
    let arcE := moonSixArc C h j
    let arcQ := moonSixArc C k j
    have heq : (h, j) ≠ (k, j) := by
      intro heq
      exact hhk (congrArg Prod.fst heq)
    have hnot :=
      pairLocalActualMoonSixPairs_not_sharePositiveSegmentAtScales_global_onItems
        C curves T U hT hU rectangles f f1 f2 center hAB.le hdelta ht
        hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
        hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
        D henlarge hscale hreference hpairwise heq
    exact pairLocalActualMoon_sameNeighbor_openSupports_disjoint_onItems
      curves items T U hT hU hpair rectangles f f1 A B M depth D
      arcE arcQ hnot

/-- All six open supports are pairwise disjoint at independent scales. -/
theorem pairLocalActualMoon_allSix_openSupports_disjointAtScales_global_onItems
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
          delta localScale referenceScale lambda)))
    {e q : K23Edge} (heq : e ≠ q) :
    ¬ (Ioo (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaLeft
          (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaRight ∩
        Ioo (D (moonSixPair C q) (moonSixPair_mem_items C q)).thetaLeft
          (D (moonSixPair C q) (moonSixPair_mem_items C q)).thetaRight).Nonempty := by
  exact (pairLocalActualMoonOpenSupportDataAtScales_global_onItems
    curves items T U hT hU hpair rectangles f f1 f2 A B M depth center D C
    hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
    hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
    hendpoint hA3 henlarge hscale hreference hpairwise).pairwise_disjoint heq

#print axioms pairLocalActualMoonOpenSupportDataAtScales_global_onItems
#print axioms pairLocalActualMoon_allSix_openSupports_disjointAtScales_global_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonOpenSupportSeparationTwoScaleRepoV2V1
