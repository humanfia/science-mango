import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41EndpointOrderedSkirtDepthV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosThreeKindAggregationV1RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualMoonFixedKindGlobalOnItemsCleanV2RepoV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensOnlyMoonListsOnItemsV1RepoV2

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensThreeKindCountGlobalOnItemsCleanV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41EndpointOrderedSkirtDepthV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MarcusTardosThreeKindAggregationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualMoonFixedKindGlobalOnItemsCleanV2
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensOnlyMoonListsOnItemsV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Explicit pair-local selected-lens count from the three actual kinds

The analytic five-curve theorem supplies the moon-face fixed-kind source.
The classification theorem proves that the other two actual list families
are empty.  These three internally produced sources feed the faithful actual
list encoding and the pure Marcus--Tardos aggregation.  No legacy global
common-reference, conditional moon facade, or forbidden-triple callback is
imported.
-/

theorem pairLocalActualSelectedLens_allKinds_fixedKindForbidsSameTriple_onItems
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
    (hdepth : forall c, 0 < depth c)
    (center : C2GraphRectangle) {domain : Set Real}
    {delta t lambda0 lambda : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta t lambda0)
    (hAB : A < B) (hdelta : 0 < delta) (ht : 0 < t)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hcommonC : forall V, V ∈ curves -> forall W, W ∈ curves ->
      tubeGraphC V = tubeGraphC W)
    (hcoefficient : forall V, V ∈ curves -> forall W, W ∈ curves ->
      V ≠ W -> 0 < tubePairCoefficientDistance V W)
    (hfDeriv : forall theta, HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, HasDerivAt f1 (f2 theta) theta)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda0) * delta <
      t / 1200)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hgraphBound : forall V, V ∈ curves -> forall theta,
      theta ∈ Icc A B -> |actualTubeGraph V f theta| <= M)
    (hcontinuous : forall V, V ∈ curves ->
      ContinuousOn (actualTubeGraph V f) (Icc A B))
    (hendpoint : EndpointValuesDistinct curves
      (fun V => actualTubeGraph V f) A B)
    (hA3 : NoTangentialGraphIntersections curves
      (fun V => actualTubeGraph V f)
      (fun V => actualTubeGraphFirst V f f1) A B)
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta t <= Real.sqrt (lambda * delta / t))
    (hreference : forall V, V ∈ curves ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB.le)
        (3 * t))
    (hpairwise : Set.Pairwise
      (items : Set (FirstGenerationCurvePair curves))
      (fun p q => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (rectangles p) (rectangles q) delta t lambda))) :
    forall k, FixedKindForbidsSameTriple
      (fun host => localAngleSelectedLensNeighborSequence
        (pairLocalActualSelectedLensLocalAngleGeometryOnItems
          curves items T U hT hU hpair rectangles f f1 A B M depth D)
        items k host) := by
  intro k
  by_cases hk : k = ProperLensKind.moonFace
  · subst k
    exact pairLocalActualMoon_fixedKindForbidsSameTriple_global_onItems
      curves items T U hT hU hpair rectangles f f1 f2 A B M depth center D
      hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient hfDeriv hf1Deriv
      hsmallScale hparameter hft hf1Lower hf1Upper hf2 hf2Continuous
      hendpoint hA3 henlarge hscale hreference hpairwise
  · exact
      pairLocalActualSelectedLens_nonMoon_fixedKindForbidsSameTriple_onItems
        curves items T U hT hU hpair rectangles f f1 hAB M depth hdepth D
        hgraphBound hcontinuous hk

theorem pairLocalActualSelectedLens_card_le_explicit_global_onItems
    {radius : NNReal} (curves : Finset (Tube radius))
    [Nonempty (FirstGenerationCurve curves)]
    (items : Finset (FirstGenerationCurvePair curves))
    (T U : FirstGenerationCurvePair curves -> Tube radius)
    (hT : forall p, T p ∈ curves) (hU : forall p, U p ∈ curves)
    (hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve T hT p,
        pairLocalActualItemSelectedSecondCurve U hU p))
    (rectangles : FirstGenerationCurvePair curves -> C2GraphRectangle)
    (f f1 f2 : Real -> Real) {A B : Real} (hAB : A < B) (M : Real)
    (center : C2GraphRectangle) {domain : Set Real}
    {delta t lambda0 lambda : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta t lambda0)
    (hdelta : 0 < delta) (ht : 0 < t) (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hcommonC : forall V, V ∈ curves -> forall W, W ∈ curves ->
      tubeGraphC V = tubeGraphC W)
    (hcoefficient : forall V, V ∈ curves -> forall W, W ∈ curves ->
      V ≠ W -> 0 < tubePairCoefficientDistance V W)
    (hfDeriv : forall theta, HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, HasDerivAt f1 (f2 theta) theta)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda0) * delta <
      t / 1200)
    (hparameter : forall theta, theta ∈ Icc A B -> |theta| <= 1)
    (hft : forall theta, theta ∈ Icc A B -> |f theta| <= 2)
    (hf1Lower : forall theta, theta ∈ Icc A B -> 1 <= |f1 theta|)
    (hf1Upper : forall theta, theta ∈ Icc A B -> |f1 theta| <= 2)
    (hf2 : forall theta, theta ∈ Icc A B -> |f2 theta| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hgraphBound : forall V, V ∈ curves -> forall theta,
      theta ∈ Icc A B -> |actualTubeGraph V f theta| <= M)
    (hendpoint : EndpointValuesDistinct curves
      (fun V => actualTubeGraph V f) A B)
    (hA3 : NoTangentialGraphIntersections curves
      (fun V => actualTubeGraph V f)
      (fun V => actualTubeGraphFirst V f f1) A B)
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta t <= Real.sqrt (lambda * delta / t))
    (hreference : forall V, V ∈ curves ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB.le)
        (3 * t))
    (hpairwise : Set.Pairwise
      (items : Set (FirstGenerationCurvePair curves))
      (fun p q => Not (compactC2SymmetricGraphLambdaComparableOn
        domain center (rectangles p) (rectangles q) delta t lambda))) :
    (items.card : Real) <= (curves.card : Real) +
      3 * (16 * (canonicalDepth (FirstGenerationCurve curves) : Real) *
          (curves.card : Real) * Real.sqrt (curves.card : Real) +
        105 * (curves.card : Real) * Real.sqrt (curves.card : Real)) := by
  let depth : FirstGenerationCurve curves -> Real :=
    endpointOrderedSkirtDepth (fun V => actualTubeGraph V f) A M
  have hdepth : forall c, 0 < depth c := by
    intro c
    exact endpointOrderedSkirtDepth_pos
      (fun V => actualTubeGraph V f) A M
      (fun V hV => hgraphBound V hV A ⟨le_rfl, hAB.le⟩) c
  have hcontinuous : forall V, V ∈ curves ->
      ContinuousOn (actualTubeGraph V f) (Icc A B) := by
    intro V _ theta _
    exact (hasDerivAt_actualTubeGraph V
      (hfDeriv theta)).continuousAt.continuousWithinAt
  have hfive :=
    pairLocalActualSelectedLens_allKinds_fixedKindForbidsSameTriple_onItems
      curves items T U hT hU hpair rectangles f f1 f2 A B M depth hdepth
      center D hAB hdelta ht hlambda0 hwidth hcommonC hcoefficient
      hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower hf1Upper hf2
      hf2Continuous hgraphBound hcontinuous hendpoint hA3 henlarge hscale
      hreference hpairwise
  have hreverse :=
    pairLocalActualSelectedLensListEncodingOnItems_pairwiseIntersectionReverse
      curves items T U hT hU hpair rectangles f f1 A B M depth D hfive
  have hbound := lensListEncoding_card_le_explicit
    (pairLocalActualSelectedLensListEncodingOnItems
      curves items T U hT hU hpair rectangles f f1 A B M depth D) hreverse
  simpa only [Fintype.card_coe] using hbound

#print axioms pairLocalActualSelectedLens_allKinds_fixedKindForbidsSameTriple_onItems
#print axioms pairLocalActualSelectedLens_card_le_explicit_global_onItems

end

end FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensThreeKindCountGlobalOnItemsCleanV1
