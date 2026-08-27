import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41K23PositiveCyclicNoAlternationContradictionCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonInnerRankCyclicTwoScaleRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonMidpointRootConsumerTwoScaleRepoV2V1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonK23ContradictionTwoScaleRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41K23PositiveCyclicNoAlternationContradictionCleanV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonInnerRankCyclicTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonMidpointRootConsumerGlobalOnItemsCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonMidpointRootConsumerTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonOpenSupportSeparationTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- A literal pair-local moon five-curve configuration remains impossible
when the local lens scale and common-reference C2 scale are independent. -/
theorem pairLocalActualMoonFiveCurveConfiguration_falseAtScales_global_onItems
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
    False := by
  let P := pairLocalActualMoonOpenSupportDataAtScales_global_onItems
    curves items T U hT hU hpair rectangles f f1 f2 A B M depth center D C
    hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
    hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
    hendpoint hA3 henlarge hscale hreference hpairwise
  have hroot : PairLocalMoonMidpointRootData P.innerSeparatedIntervals
      P.hostGraph P.neighborGraph A B := by
    exact pairLocalActualMoon_midpointRootDataAtScales_global_onItems
      curves items T U hT hU hpair rectangles f f1 f2 A B M depth center D C
      hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hendpoint hA3 henlarge hscale hreference hpairwise
  have hno := hroot.not_rankAlternation
  have hcyclicRank :=
    pairLocalActualMoon_innerRank_hostCyclicPositiveAtScales_global_onItems
      curves items T U hT hU hpair rectangles f f1 f2 A B M depth center D C
      hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hendpoint hA3 henlarge hscale hreference hpairwise
  apply false_of_positiveCyclic_and_noAlternation P.innerSeparatedIntervals
      ?_ (hno.1) (hno.2)
  intro h
  simpa [
    FamilyStickyCinematicL32Prop41K23PositiveCyclicPermutationKernelDecideV1.HostCyclicPositive,
    FamilyStickyCinematicL32Prop41PairLocalMoonCyclicPortRankTransferCleanV2.HostRankCyclicPositive]
    using hcyclicRank h

#print axioms pairLocalActualMoonFiveCurveConfiguration_falseAtScales_global_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonK23ContradictionTwoScaleRepoV2V1
