import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualLensBoundaryNonOverlapTwoScaleRepoV2V1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualMoonSixBoundaryNonOverlapTwoScaleRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32Prop41ActualBoundarySharedTubeExtractionGlobalCleanV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41GraphLensBoundarySegmentOverlapV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MoonFiveCurveConfigurationCleanV1
open FamilyStickyCinematicL32Prop41MoonSixArcIndexCleanV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensBoundaryNonOverlapTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-- Nonoverlap for the six selected moon boundaries with independent local
and reference scales. -/
theorem pairLocalActualMoonSixPairs_not_sharePositiveSegmentAtScales_global_onItems
    {point curve : Type*} [DecidableEq curve] {curves : Finset curve}
    {G : SelectedFixedSlotLensLocalAngleGeometry point curve curves}
    {items : Finset (FirstGenerationCurvePair curves)}
    {leftHost rightHost x y z : FirstGenerationCurve curves}
    (C : MoonFiveCurveConfiguration G items leftHost rightHost x y z)
    {radius : NNReal} (tubes : Finset (Tube radius))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ tubes) (hU : forall p, U p ∈ tubes)
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 f2 : Real -> Real) (center : C2GraphRectangle)
    {domain : Set Real}
    {A B delta localScale referenceScale lambda0 lambda : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hcommonC : forall V, V ∈ tubes -> forall W, W ∈ tubes ->
      tubeGraphC V = tubeGraphC W)
    (hcoefficient : forall V, V ∈ tubes -> forall W, W ∈ tubes ->
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
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta localScale lambda0)
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta localScale <=
      Real.sqrt (lambda * delta / localScale))
    (hreference : forall V, V ∈ tubes ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
        (3 * referenceScale))
    (hpairwise : Set.Pairwise
      (items : Set (FirstGenerationCurvePair curves))
      (fun p q => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (rectangles p) (rectangles q)
          delta localScale referenceScale lambda)))
    {e q : Fin 2 × Fin 3} (heq : e ≠ q) :
    Not (sharePositiveGraphSegment
      (actualPairGraphBoundary
        (T (moonSixPair C e)) (U (moonSixPair C e)) f
        (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaLeft
        (D (moonSixPair C e) (moonSixPair_mem_items C e)).thetaRight)
      (actualPairGraphBoundary
        (T (moonSixPair C q)) (U (moonSixPair C q)) f
        (D (moonSixPair C q) (moonSixPair_mem_items C q)).thetaLeft
        (D (moonSixPair C q) (moonSixPair_mem_items C q)).thetaRight)) := by
  have hpairsNe : moonSixPair C e ≠ moonSixPair C q := by
    intro hpairs
    exact heq ((moonSixPair_injective C) hpairs)
  exact
    not_sharePositiveSegment_of_pairLocalActualData_and_incomparableAtScales_global
      tubes
      (T (moonSixPair C e)) (U (moonSixPair C e))
      (T (moonSixPair C q)) (U (moonSixPair C q))
      (hT (moonSixPair C e)) (hU (moonSixPair C e))
      (hT (moonSixPair C q)) (hU (moonSixPair C q))
      f f1 f2 center
      (rectangles (moonSixPair C e)) (rectangles (moonSixPair C q))
      hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient
      hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower hf1Upper
      hf2 hf2Continuous
      (D (moonSixPair C e) (moonSixPair_mem_items C e))
      (D (moonSixPair C q) (moonSixPair_mem_items C q))
      henlarge hscale hreference
      (hpairwise (moonSixPair_mem_items C e) (moonSixPair_mem_items C q)
        hpairsNe)

#print axioms pairLocalActualMoonSixPairs_not_sharePositiveSegmentAtScales_global_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualMoonSixBoundaryNonOverlapTwoScaleRepoV2V1
