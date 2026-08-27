import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonFixedKindTwoScaleRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensTwoScaleMoonCoreRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonFixedKindTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Automatic RepoV2 two-scale Moon core

This is the terminal analytic adapter.  It packages the completed
two-scale boundary/open-support/rank/midpoint/K23 chain into the exact
proposition consumed by the selected-lens counter.  In particular it is a
theorem, not a callback field or an axiom.
-/

/-- The ordinary pair-local analytic fields automatically produce the
two-scale Moon core required by the counting adapter. -/
theorem pairLocalActualSelectedLensTwoScaleMoonCore_of_geometry
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
    (center : C2GraphRectangle) (domain : Set Real)
    {delta localScale referenceScale lambda0 lambda : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta localScale lambda0)
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
      Real.sqrt (lambda * delta / localScale)) :
    PairLocalActualSelectedLensTwoScaleMoonCore
      curves items T U hT hU hpair rectangles f f1 f2 A B M depth center
        domain delta localScale referenceScale lambda0 lambda D hAB.le
          hfDeriv hf1Deriv := by
  unfold PairLocalActualSelectedLensTwoScaleMoonCore
  intro hreference hpairwise
  exact pairLocalActualMoon_fixedKindForbidsSameTripleAtScales_global_onItems
    curves items T U hT hU hpair rectangles f f1 f2 A B M depth center D
    hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
    hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
    hendpoint hA3 henlarge hscale hreference hpairwise

#print axioms pairLocalActualSelectedLensTwoScaleMoonCore_of_geometry

end

end FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensTwoScaleMoonCoreRepoV2V1
