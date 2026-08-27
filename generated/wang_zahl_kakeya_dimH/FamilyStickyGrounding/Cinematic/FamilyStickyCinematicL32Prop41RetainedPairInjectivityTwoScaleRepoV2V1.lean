import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41PairLocalActualLensDynamicSharedTubeComparabilityTwoScaleRepoV2V1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41RetainedPairInjectivityTwoScaleRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualPairRootSupportLocalizationV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensDynamicSharedTubeComparabilityTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

/-!
# Injectivity of retained unordered tube-pair labels

Two pair-local records for the same unordered actual-tube pair have
overlapping exact-root supports, including when their stored orientations
are reversed.  The existing dynamic shared-tube comparison theorem then
makes their rectangles comparable.  Consequently a pairwise incomparable
retained rectangle family has injective unordered-pair labels; injectivity is
therefore a geometric consequence rather than an independent reindexing
hypothesis.
-/

/-- Exact two-root supports overlap when the underlying actual-tube pairs
agree as unordered pairs.  The reversed orientation is handled directly
from the literal exact-root-set fields. -/
theorem lensSupports_overlap_of_unorderedPair_eq
    {radius : NNReal} {T1 U1 T2 U2 : Tube radius}
    {f : Real -> Real} {R S : C2GraphRectangle}
    {A B delta localScale lambda0 : Real}
    (D1 : PairLocalActualLensRectangleData T1 U1 f R
      A B delta localScale lambda0)
    (D2 : PairLocalActualLensRectangleData T2 U2 f S
      A B delta localScale lambda0)
    (hpair : s(T1, U1) = s(T2, U2)) :
    (D1.lensSupport ∩ D2.lensSupport).Nonempty := by
  rw [Sym2.eq_iff] at hpair
  rcases hpair with hsame | hreverse
  · rcases hsame with ⟨hT, hU⟩
    subst T2
    subst U2
    exact D1.lensSupports_overlap_samePair D2
  · rcases hreverse with ⟨hT, hU⟩
    subst U2
    subst T2
    have hroot : D1.thetaLeft ∈ pairLocalActualRootSet U1 T1 f A B :=
      ⟨D1.thetaLeft_mem, D1.root_left.symm⟩
    rw [D2.exact_root_set] at hroot
    have hcases : D1.thetaLeft = D2.thetaLeft ∨
        D1.thetaLeft = D2.thetaRight := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hroot
    refine ⟨D1.thetaLeft, ?_, ?_⟩
    · exact ⟨le_rfl, D1.theta_order.le⟩
    · rcases hcases with hleft | hright
      · rw [hleft]
        exact ⟨le_rfl, D2.theta_order.le⟩
      · rw [hright]
        exact ⟨D2.theta_order.le, le_rfl⟩

/-- Enlarge a literal pair tangency and identify its graph with the C2
rectangle built from the selected actual tube. -/
theorem tangent_to_pairLocalTubeReference_of_tangent_enlarged
    {radius : NNReal} (V : Tube radius)
    (f f1 f2 : Real -> Real) (R : C2GraphRectangle)
    {A B delta lambda0 lambda : Real}
    (hAB : A <= B)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (htangent : R.carrier delta ⊆
      cinematicVerticalNeighborhood
        (cinematicTraceValue f (tubeGraphA V) (tubeGraphB V)
          (tubeGraphC V) (tubeGraphD V))
        R.rectangle.base (2 * lambda0 * delta))
    (henlarge : 2 * lambda0 * delta <= lambda * delta) :
    R.carrier delta ⊆
      cinematicVerticalNeighborhood
        (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv A B hAB).rectangle.graph
        R.rectangle.base (lambda * delta) := by
  intro q hq
  have hqTrace := htangent hq
  refine ⟨hqTrace.1, ?_⟩
  simpa [pairLocalTubeReference, tubeC2GraphRectangle] using
    hqTrace.2.trans henlarge

/-- Two pair-local rectangles indexed by the same unordered actual-tube pair
are comparable.  This is the minimal geometric bridge needed by retained
pair reindexing. -/
theorem compactC2Comparable_of_pairLocalData_and_sameUnorderedPair
    {radius : NNReal} (T1 U1 T2 U2 : Tube radius)
    (f f1 f2 : Real -> Real) (center R S : C2GraphRectangle)
    {domain : Set Real} {A B delta localScale referenceScale lambda0 lambda : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda0) * delta <
      localScale / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (D1 : PairLocalActualLensRectangleData T1 U1 f R
      A B delta localScale lambda0)
    (D2 : PairLocalActualLensRectangleData T2 U2 f S
      A B delta localScale lambda0)
    (hpair : s(T1, U1) = s(T2, U2))
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta localScale <= Real.sqrt (lambda * delta / localScale))
    (hreference : InPointwiseC2BallOn domain center
      (pairLocalTubeReference T1 f f1 f2 hfDeriv hf1Deriv A B hAB)
      (3 * referenceScale)) :
    compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center R S delta localScale referenceScale lambda := by
  have hsupport := lensSupports_overlap_of_unorderedPair_eq D1 D2 hpair
  have htangentR :=
    tangent_to_pairLocalTubeReference_of_tangent_enlarged
      T1 f f1 f2 R hAB hfDeriv hf1Deriv D1.tangent_first henlarge
  rw [Sym2.eq_iff] at hpair
  rcases hpair with hsame | hreverse
  · rcases hsame with ⟨hT, hU⟩
    subst T2
    subst U2
    exact compactC2ComparableAtScales_of_pairLocalData_and_dynamicSharedTube
      T1 U1 T1 U1 T1 f f1 f2 center R S hAB hdelta ht hlambda0
      hwidth hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous D1 D2 hsupport hscale htangentR
      (tangent_to_pairLocalTubeReference_of_tangent_enlarged
        T1 f f1 f2 S hAB hfDeriv hf1Deriv D2.tangent_first henlarge)
      hreference
  · rcases hreverse with ⟨hT, hU⟩
    subst U2
    subst T2
    exact compactC2ComparableAtScales_of_pairLocalData_and_dynamicSharedTube
      T1 U1 U1 T1 T1 f f1 f2 center R S hAB hdelta ht hlambda0
      hwidth hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous D1 D2 hsupport hscale htangentR
      (tangent_to_pairLocalTubeReference_of_tangent_enlarged
        T1 f f1 f2 S hAB hfDeriv hf1Deriv D2.tangent_second henlarge)
      hreference

/-- Pairwise incomparability of the retained rectangles forces injectivity
of their literal unordered actual-tube-pair labels. -/
theorem retainedUnorderedPairInjective_of_pairwise_incomparable
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (f f1 f2 : Real -> Real) (center : C2GraphRectangle)
    (rectangles : alpha -> C2GraphRectangle)
    {domain : Set Real} {A B delta localScale referenceScale lambda0 lambda : Real}
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda0) * delta <
      localScale / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (D : forall i, i ∈ fiber ->
      PairLocalActualLensRectangleData (T i) (U i) f (rectangles i)
        A B delta localScale lambda0)
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta localScale <= Real.sqrt (lambda * delta / localScale))
    (hreference : forall i, i ∈ fiber ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference (T i) f f1 f2
          hfDeriv hf1Deriv A B hAB) (3 * referenceScale))
    (hpairwise : Set.Pairwise (fiber : Set alpha)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (rectangles i) (rectangles j) delta localScale referenceScale lambda))) :
    RetainedUnorderedPairInjective fiber T U := by
  intro i j hpairSubtype
  apply Subtype.ext
  by_contra hij
  have hpairTube : s(T i.1, U i.1) = s(T j.1, U j.1) := by
    rw [Sym2.eq_iff] at hpairSubtype ⊢
    rcases hpairSubtype with hsame | hreverse
    · exact Or.inl ⟨congrArg Subtype.val hsame.1,
        congrArg Subtype.val hsame.2⟩
    · exact Or.inr ⟨congrArg Subtype.val hreverse.1,
        congrArg Subtype.val hreverse.2⟩
  apply hpairwise i.2 j.2 hij
  exact compactC2Comparable_of_pairLocalData_and_sameUnorderedPair
    (T i.1) (U i.1) (T j.1) (U j.1) f f1 f2 center
    (rectangles i.1) (rectangles j.1) hAB hdelta ht hlambda0 hwidth
    hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower hf1Upper
    hf2 hf2Continuous (D i.1 i.2) (D j.1 j.2) hpairTube henlarge
    hscale (hreference i.1 i.2)

/-- Build the total endpoint interface directly from pair-local geometry and
pairwise incomparability.  Neither unordered-pair injectivity nor pair
non-diagonality remains as a public reindexing assumption: the former is the
preceding theorem, while the latter follows from the positive `localScale` lower
bound in each pair-local record. -/
theorem exists_total_retainedPairLocalEndpointInterface_of_pairwise_incomparable
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f f1 f2 : Real -> Real) (center : C2GraphRectangle)
    {domain : Set Real} (A B delta localScale referenceScale lambda0 lambda : Real)
    (hfiber : fiber.Nonempty)
    (hAB : A <= B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda0 : 1 <= lambda0)
    (hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda0) * delta <
      localScale / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (D : forall i, i ∈ fiber ->
      PairLocalActualLensRectangleData (T i) (U i) f
        (sourceRectangles i) A B delta localScale lambda0)
    (henlarge : 2 * lambda0 * delta <= lambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda0) delta localScale <= Real.sqrt (lambda * delta / localScale))
    (hreference : forall i, i ∈ fiber ->
      InPointwiseC2BallOn domain center
        (pairLocalTubeReference (T i) f f1 f2
          hfDeriv hf1Deriv A B hAB) (3 * referenceScale))
    (hpairwise : Set.Pairwise (fiber : Set alpha)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (sourceRectangles i) (sourceRectangles j)
          delta localScale referenceScale lambda))) :
    Nonempty (RetainedPairLocalEndpointInterface
      fiber T U sourceRectangles f A B delta localScale lambda0) := by
  have hpairNe : forall i, i ∈ fiber -> T i ≠ U i := by
    intro i hi hTU
    have hlower := (D i hi).coefficient_lower
    rw [hTU] at hlower
    have hzero : tubePairCoefficientDistance (U i) (U i) = 0 := by
      simp [tubePairCoefficientDistance, tubePairDeltaA,
        tubePairDeltaB, tubePairDeltaD, coefficientDistance]
    rw [hzero] at hlower
    exact (not_lt_of_ge hlower) ht
  have hpairInjective : RetainedUnorderedPairInjective fiber T U :=
    retainedUnorderedPairInjective_of_pairwise_incomparable
      fiber T U f f1 f2 center sourceRectangles hAB hdelta ht hlambda0
      hwidth hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower
      hf1Upper hf2 hf2Continuous D henlarge hscale hreference hpairwise
  exact exists_total_retainedPairLocalEndpointInterface
    fiber T U sourceRectangles f A B delta localScale lambda0
      hfiber hpairNe hpairInjective D

#print axioms lensSupports_overlap_of_unorderedPair_eq
#print axioms tangent_to_pairLocalTubeReference_of_tangent_enlarged
#print axioms compactC2Comparable_of_pairLocalData_and_sameUnorderedPair
#print axioms retainedUnorderedPairInjective_of_pairwise_incomparable
#print axioms exists_total_retainedPairLocalEndpointInterface_of_pairwise_incomparable

end

end FamilyStickyCinematicL32Prop41RetainedPairInjectivityTwoScaleRepoV2V1
