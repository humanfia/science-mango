import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41CommonReferenceIndependentScaleV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set

namespace FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41CommonReferenceComparabilityV1
open FamilyStickyCinematicL32Prop41CommonReferenceIndependentScaleV1
open FamilyStickyCinematicL32Prop41EndpointOrderedSkirtDepthV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41LensOverlapBaseDiameterV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
open FamilyStickyCinematicL32Prop41MarcusTardosThreeKindAggregationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensListEncodingOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensOnlyMoonListsOnItemsV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainFiniteContainerV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Two-scale counting adapter for Proposition 4.1

The current reduced selected-family counter uses the same parameter `t` in
two genuinely different places:

* local lens geometry (rectangle length, localization, tangency and
  comparison enlargement), and
* membership of the common container in a pointwise `C2` ball of radius
  `3 * t`.

The second occurrence is not merely a field of
`SelectedSubfamilyFiniteGeneralPositionCountingPackage`: it is part of
`compactC2SymmetricGraphLambdaComparableOn`, and is used by the moon-face
forbidden-triple proof.  The non-moon classification and the final
Marcus--Tardos list count do not use it.

This module therefore introduces the honest two-scale comparability
relation, proves the common-reference localization lemmas at independent
scales, and exposes the exact remaining analytic seam: a two-scale
moon-face `FixedKindForbidsSameTriple` callback.  Once that callback is
provided, the existing list encoder and cardinality endpoint are reused
without any change to their local scale.
-/

/-- Compact-C2 comparability with separate local and reference scales.
Only `localScale` controls the enlarged base length; only `referenceScale`
controls the common `C2` ball. -/
def compactC2SymmetricGraphLambdaComparableOnAtScales
    (domain : Set Real) (center R S : C2GraphRectangle)
    (delta localScale referenceScale lambda : Real) : Prop :=
  exists container : C2GraphRectangle,
    container.rectangle.right - container.rectangle.left =
      Real.sqrt (lambda * delta / localScale) ∧
    R.carrier delta ∪ S.carrier delta ⊆
      container.carrier (lambda * delta) ∧
    InPointwiseC2BallOn domain center container (3 * referenceScale)

/-- At equal scales the adapter is definitionally the old relation. -/
theorem compactC2SymmetricGraphLambdaComparableOnAtScales_same
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta t lambda : Real} :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta t t lambda ↔
    compactC2SymmetricGraphLambdaComparableOn
      domain center R S delta t lambda := by
  rfl

/-- Two-scale compact-C2 comparability remains symmetric. -/
theorem compactC2SymmetricGraphLambdaComparableOnAtScales_symm
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale lambda : Real}
    (h : compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center S R delta localScale referenceScale lambda := by
  rcases h with ⟨container, hlength, hcontain, hball⟩
  refine ⟨container, hlength, ?_, hball⟩
  simpa [union_comm] using hcontain

/-- Pointwise C2-ball membership is monotone in its radius. -/
theorem inPointwiseC2BallOn_mono_radius
    {domain : Set Real} {center R : C2GraphRectangle} {r s : Real}
    (hrs : r ≤ s) (hR : InPointwiseC2BallOn domain center R r) :
    InPointwiseC2BallOn domain center R s := by
  intro z hz
  exact ⟨(hR z hz).1.trans hrs,
    (hR z hz).2.1.trans hrs,
    (hR z hz).2.2.trans hrs⟩

/-- Increasing only the reference scale preserves two-scale comparability. -/
theorem compactC2SymmetricGraphLambdaComparableOnAtScales_mono_reference
    {domain : Set Real} {center R S : C2GraphRectangle}
    {delta localScale referenceScale₁ referenceScale₂ lambda : Real}
    (hscale : referenceScale₁ ≤ referenceScale₂)
    (h : compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale₁ lambda) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale₂ lambda := by
  rcases h with ⟨container, hlength, hcontain, hball⟩
  refine ⟨container, hlength, hcontain, ?_⟩
  apply inPointwiseC2BallOn_mono_radius (r := 3 * referenceScale₁)
    (s := 3 * referenceScale₂)
  · gcongr
  · exact hball

/-- A diameter-controlled pair of bases tangent to one reference produces
two-scale comparability.  This is the independent-scale version of
`compactC2Comparable_of_commonReference_and_baseUnionDiameter`. -/
theorem compactC2ComparableAtScales_of_commonReference_and_baseUnionDiameter
    {domain piece : Set Real} {center reference R S : C2GraphRectangle}
    {delta localScale referenceScale lambda : Real}
    (hbaseR : R.rectangle.base ⊆ piece)
    (hbaseS : S.rectangle.base ⊆ piece)
    (hpieceDiameter : forall x, x ∈ piece -> forall y, y ∈ piece ->
      dist x y <= Real.sqrt (lambda * delta / localScale))
    (htangentR : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        R.rectangle.base (lambda * delta))
    (htangentS : S.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        S.rectangle.base (lambda * delta))
    (hreference : InPointwiseC2BallOn domain center reference
      (3 * referenceScale)) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda := by
  classical
  let pairRectangles : Bool -> C2GraphRectangle := fun b =>
    if b then R else S
  have hbasePair : forall b, b ∈ (Finset.univ : Finset Bool) ->
      (pairRectangles b).rectangle.base ⊆ piece := by
    intro b _hb
    cases b <;> simp [pairRectangles, hbaseR, hbaseS]
  have htangentPair : forall b, b ∈ (Finset.univ : Finset Bool) ->
      (pairRectangles b).carrier delta ⊆
        cinematicVerticalNeighborhood reference.rectangle.graph
          (pairRectangles b).rectangle.base (lambda * delta) := by
    intro b _hb
    cases b <;> simp [pairRectangles, htangentR, htangentS]
  rcases exists_rebased_container_of_bases_in_diameter_piece_on
      (Finset.univ : Finset Bool) pairRectangles reference piece domain
      (length := Real.sqrt (lambda * delta / localScale))
      (delta := delta) (V := lambda * delta)
      (Real.sqrt_nonneg _) hbasePair hpieceDiameter htangentPair with
    ⟨container, hlength, hball, hcontain⟩
  refine ⟨container, hlength, ?_,
    hball center (3 * referenceScale) hreference⟩
  intro q hq
  rcases hq with hqR | hqS
  · exact hcontain true (Finset.mem_univ _) (by
      simpa [pairRectangles] using hqR)
  · exact hcontain false (Finset.mem_univ _) (by
      simpa [pairRectangles] using hqS)

/-- Lens-support overlap retains the local scale in all localization and
base-length terms while using the independent scale only for the common
reference ball. -/
theorem compactC2ComparableAtScales_of_lensSupport_overlap
    {domain : Set Real} {center reference R S : C2GraphRectangle}
    {lensSupportR lensSupportS : Set Real}
    {criticalR criticalS radius delta localScale referenceScale lambda : Real}
    (hradius : 0 <= radius)
    (hbaseR : forall x, x ∈ R.rectangle.base ->
      dist x criticalR <= radius)
    (hbaseS : forall x, x ∈ S.rectangle.base ->
      dist x criticalS <= radius)
    (hlensR : forall x, x ∈ lensSupportR ->
      dist x criticalR <= radius)
    (hlensS : forall x, x ∈ lensSupportS ->
      dist x criticalS <= radius)
    (hoverlap : (lensSupportR ∩ lensSupportS).Nonempty)
    (hscale : 4 * radius <= Real.sqrt (lambda * delta / localScale))
    (htangentR : R.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        R.rectangle.base (lambda * delta))
    (htangentS : S.carrier delta ⊆
      cinematicVerticalNeighborhood reference.rectangle.graph
        S.rectangle.base (lambda * delta))
    (hreference : InPointwiseC2BallOn domain center reference
      (3 * referenceScale)) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda := by
  have hdiameter :=
    base_union_diameter_le_four_mul_of_lensSupport_overlap
      R.rectangle.base S.rectangle.base lensSupportR lensSupportS
      criticalR criticalS radius hradius hbaseR hbaseS hlensR hlensS hoverlap
  apply compactC2ComparableAtScales_of_commonReference_and_baseUnionDiameter
    (piece := R.rectangle.base ∪ S.rectangle.base)
    (center := center) (reference := reference)
  · exact subset_union_left
  · exact subset_union_right
  · intro x hx y hy
    exact (hdiameter x hx y hy).trans hscale
  · exact htangentR
  · exact htangentS
  · exact hreference

/-- The exact analytic seam left by the old one-scale implementation.
All local lens data retain `localScale`.  The two inputs consumed by the
missing moon proof use `referenceScale` only in the C2-ball component.

This is intentionally a callback proposition, not an axiom: a future
generalization of
`pairLocalActualMoon_fixedKindForbidsSameTriple_global_onItems` proves it,
and the counting adapter below consumes it. -/
def PairLocalActualSelectedLensTwoScaleMoonCore
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
    (delta localScale referenceScale lambda0 lambda : Real)
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta localScale lambda0)
    (hAB : A <= B)
    (hfDeriv : forall theta, HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, HasDerivAt f1 (f2 theta) theta) : Prop :=
  (forall V, V ∈ curves ->
    InPointwiseC2BallOn domain center
      (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB)
      (3 * referenceScale)) ->
  Set.Pairwise (items : Set (FirstGenerationCurvePair curves))
    (fun p q => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center (rectangles p) (rectangles q)
        delta localScale referenceScale lambda)) ->
  FixedKindForbidsSameTriple
    (fun host => localAngleSelectedLensNeighborSequence
      (pairLocalActualSelectedLensLocalAngleGeometryOnItems
        curves items T U hT hU hpair rectangles f f1 A B M depth D)
      items ProperLensKind.moonFace host)

/-- Two-scale selected-lens count.  The old non-moon proof and the old
Marcus--Tardos endpoint are reused verbatim; only the precisely isolated
two-scale moon callback is new input. -/
theorem pairLocalActualSelectedLens_card_le_explicit_global_onItems_of_twoScaleMoonCore
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
    {delta localScale referenceScale lambda0 lambda : Real}
    (D : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (T p) (U p) f (rectangles p) A B delta localScale lambda0)
    (hfDeriv : forall theta, HasDerivAt f (f1 theta) theta)
    (hf1Deriv : forall theta, HasDerivAt f1 (f2 theta) theta)
    (hgraphBound : forall V, V ∈ curves -> forall theta,
      theta ∈ Icc A B -> |actualTubeGraph V f theta| <= M)
    (hreference : forall V, V ∈ curves ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB.le)
        (3 * referenceScale))
    (hpairwise : Set.Pairwise
      (items : Set (FirstGenerationCurvePair curves))
      (fun p q => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (rectangles p) (rectangles q)
          delta localScale referenceScale lambda)))
    (hmoonCore : forall depth : FirstGenerationCurve curves -> Real,
      PairLocalActualSelectedLensTwoScaleMoonCore
        curves items T U hT hU hpair rectangles f f1 f2 A B M depth
          center domain delta localScale referenceScale lambda0 lambda D
          hAB.le hfDeriv hf1Deriv) :
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
  have hmoon : FixedKindForbidsSameTriple
      (fun host => localAngleSelectedLensNeighborSequence
        (pairLocalActualSelectedLensLocalAngleGeometryOnItems
          curves items T U hT hU hpair rectangles f f1 A B M depth D)
        items ProperLensKind.moonFace host) :=
    by
      have hcore := hmoonCore depth
      unfold PairLocalActualSelectedLensTwoScaleMoonCore at hcore
      exact hcore hreference hpairwise
  have hall : forall k, FixedKindForbidsSameTriple
      (fun host => localAngleSelectedLensNeighborSequence
        (pairLocalActualSelectedLensLocalAngleGeometryOnItems
          curves items T U hT hU hpair rectangles f f1 A B M depth D)
        items k host) := by
    intro k
    by_cases hk : k = ProperLensKind.moonFace
    · subst k
      exact hmoon
    · exact
        pairLocalActualSelectedLens_nonMoon_fixedKindForbidsSameTriple_onItems
          curves items T U hT hU hpair rectangles f f1 hAB M depth hdepth D
          hgraphBound hcontinuous hk
  have hreverse :=
    pairLocalActualSelectedLensListEncodingOnItems_pairwiseIntersectionReverse
      curves items T U hT hU hpair rectangles f f1 A B M depth D hall
  have hbound := lensListEncoding_card_le_explicit
    (pairLocalActualSelectedLensListEncodingOnItems
      curves items T U hT hU hpair rectangles f f1 A B M depth D) hreverse
  simpa only [Fintype.card_coe] using hbound

/-!
The preceding theorem pinpoints the minimum core generalization.  Extending
the outer selected-family package additionally requires transporting its
source `Pairwise` field to endpoint items with the new relation; no change is
needed in the random-sampling, depth, or Marcus--Tardos layers.
-/

#print axioms compactC2SymmetricGraphLambdaComparableOnAtScales
#print axioms compactC2SymmetricGraphLambdaComparableOnAtScales_same
#print axioms compactC2SymmetricGraphLambdaComparableOnAtScales_symm
#print axioms inPointwiseC2BallOn_mono_radius
#print axioms compactC2SymmetricGraphLambdaComparableOnAtScales_mono_reference
#print axioms compactC2ComparableAtScales_of_commonReference_and_baseUnionDiameter
#print axioms compactC2ComparableAtScales_of_lensSupport_overlap
#print axioms PairLocalActualSelectedLensTwoScaleMoonCore
#print axioms pairLocalActualSelectedLens_card_le_explicit_global_onItems_of_twoScaleMoonCore

end

end FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
