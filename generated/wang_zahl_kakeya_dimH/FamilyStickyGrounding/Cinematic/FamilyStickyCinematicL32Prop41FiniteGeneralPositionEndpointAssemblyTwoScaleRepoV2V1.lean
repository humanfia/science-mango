import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RetainedPairInjectivityTwoScaleRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Lemma57TubeDistanceBoundsV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensThreeKindCountGlobalOnItemsCleanV1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41PairLocalActualSelectedLensLocalAngleGeometryOnItemsV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41RectangularSkirtJordanSourceV1
open FamilyStickyCinematicL32Prop41RetainedPairInjectivityTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32RectangleTangencyV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32TubeC2GraphRectangleV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Final finite-general-position endpoint assembly

This module keeps the literal perturbed actual tubes throughout the retained
pair reindexing.  In particular, A2--A3, exact pair-local data, unordered-pair
injectivity, and the endpoint item family all refer to the same tubes.
-/

/-- First member of a retained pair after the individual general-position
translation. -/
def perturbedRetainedFirstTube
    {alpha : Type*} {radius : NNReal}
    (weight : Tube radius -> Real) (epsilon : Real)
    (T : alpha -> Tube radius) (i : alpha) : Tube radius :=
  individuallyTracePerturbedTube weight epsilon (T i)

/-- Second member of the same perturbed retained pair. -/
def perturbedRetainedSecondTube
    {alpha : Type*} {radius : NNReal}
    (weight : Tube radius -> Real) (epsilon : Real)
    (U : alpha -> Tube radius) (i : alpha) : Tube radius :=
  individuallyTracePerturbedTube weight epsilon (U i)

/-- The literal actual-tube family occurring in the perturbed retained
pairs. -/
def perturbedRetainedTubeFamily
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (weight : Tube radius -> Real) (epsilon : Real) : Finset (Tube radius) :=
  retainedPairTubeFamily fiber
    (perturbedRetainedFirstTube weight epsilon T)
    (perturbedRetainedSecondTube weight epsilon U)

/-- Perturbing the union of the two retained projections is exactly the
union of their perturbed projections. -/
theorem perturbedRetainedTubeFamily_eq_individuallyTracePerturbedTubeFamily
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (weight : Tube radius -> Real) (epsilon : Real) :
    perturbedRetainedTubeFamily fiber T U weight epsilon =
      individuallyTracePerturbedTubeFamily
        (retainedPairTubeFamily fiber T U) weight epsilon := by
  ext V
  simp only [perturbedRetainedTubeFamily, perturbedRetainedFirstTube,
    perturbedRetainedSecondTube, retainedPairTubeFamily,
    individuallyTracePerturbedTubeFamily, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨T i, Or.inl ⟨i, hi, rfl⟩, rfl⟩
    · exact ⟨U i, Or.inr ⟨i, hi, rfl⟩, rfl⟩
  · rintro ⟨V0, (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩

/-- A common `c` slice is preserved by every individual vertical
translation and by the retained-pair union. -/
theorem perturbedRetainedTubeFamily_commonC
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (weight : Tube radius -> Real) (epsilon : Real)
    (hcommonC : forall V, V ∈ retainedPairTubeFamily fiber T U -> forall W,
      W ∈ retainedPairTubeFamily fiber T U -> tubeGraphC V = tubeGraphC W) :
    forall V, V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
      forall W, W ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
        tubeGraphC V = tubeGraphC W := by
  intro V hV W hW
  rw [perturbedRetainedTubeFamily_eq_individuallyTracePerturbedTubeFamily,
    individuallyTracePerturbedTubeFamily, Finset.mem_image] at hV hW
  obtain ⟨V0, hV0, rfl⟩ := hV
  obtain ⟨W0, hW0, rfl⟩ := hW
  simpa only [individuallyTracePerturbedTube,
    tubeGraphC_traceTranslateTube] using hcommonC V0 hV0 W0 hW0

/-- Endpoint distinctness plus a common `c` slice forces positive reduced
coefficient distance for every distinct pair. -/
theorem tubePairCoefficientDistance_pos_of_endpointDistinct_commonC
    {radius : NNReal} (curves : Finset (Tube radius))
    (f : Real -> Real) (A B : Real)
    (hendpoint : EndpointValuesDistinct curves
      (fun V => actualTubeGraph V f) A B)
    (hcommonC : forall V, V ∈ curves -> forall W, W ∈ curves ->
      tubeGraphC V = tubeGraphC W) :
    forall V, V ∈ curves -> forall W, W ∈ curves -> V ≠ W ->
      0 < tubePairCoefficientDistance V W := by
  intro V hV W hW hVW
  have hnonneg := tubePairCoefficientDistance_nonneg V W
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hzero' : tubePairCoefficientDistance V W = 0 := hzero.symm
  have haAbs : |tubePairDeltaA V W| = 0 := by
    simp only [tubePairCoefficientDistance, coefficientDistance] at hzero'
    nlinarith [abs_nonneg (tubePairDeltaA V W),
      abs_nonneg (tubePairDeltaB V W), abs_nonneg (tubePairDeltaD V W)]
  have hbAbs : |tubePairDeltaB V W| = 0 := by
    simp only [tubePairCoefficientDistance, coefficientDistance] at hzero'
    nlinarith [abs_nonneg (tubePairDeltaA V W),
      abs_nonneg (tubePairDeltaB V W), abs_nonneg (tubePairDeltaD V W)]
  have hdAbs : |tubePairDeltaD V W| = 0 := by
    simp only [tubePairCoefficientDistance, coefficientDistance] at hzero'
    nlinarith [abs_nonneg (tubePairDeltaA V W),
      abs_nonneg (tubePairDeltaB V W), abs_nonneg (tubePairDeltaD V W)]
  have ha : tubeGraphA V = tubeGraphA W := by
    rw [abs_eq_zero, tubePairDeltaA, sub_eq_zero] at haAbs
    exact haAbs
  have hb : tubeGraphB V = tubeGraphB W := by
    rw [abs_eq_zero, tubePairDeltaB, sub_eq_zero] at hbAbs
    exact hbAbs
  have hd : tubeGraphD V = tubeGraphD W := by
    rw [abs_eq_zero, tubePairDeltaD, sub_eq_zero] at hdAbs
    exact hdAbs
  have hc := hcommonC V hV W hW
  simp only [tubeGraphC] at hc
  have hgraph : actualTubeGraph V f A = actualTubeGraph W f A := by
    simp only [actualTubeGraph, skirtTubeGraphA, skirtTubeGraphB,
      skirtTubeGraphC, skirtTubeGraphD, tubeGraphA, tubeGraphB,
      tubeGraphC, tubeGraphD] at ha hb hd ⊢
    rw [ha, hb, hc, hd]
  exact hVW (hendpoint.1 hV hW hgraph)


/-- The final retained endpoint package.  All fields use the same literal
individually translated actual tubes.  The final field is the transported
pairwise-incomparability statement required by the on-items lens counter. -/
structure PerturbedRetainedPairEndpointAssemblyAtScales
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (weight : Tube radius -> Real) (f f1 : Real -> Real)
    (center : C2GraphRectangle) (domain : Set Real)
    (A B delta localScale referenceScale lambda1 comparisonLambda externalTolerance : Real) where
  fiber_nonempty : fiber.Nonempty
  epsilon : Real
  epsilon_pos : 0 < epsilon
  epsilon_lt_external : epsilon < externalTolerance
  perturb_injective : Set.InjOn
    (individuallyTracePerturbedTube weight epsilon)
    (retainedPairTubeFamily fiber T U : Set (Tube radius))
  family_card_eq :
    (perturbedRetainedTubeFamily fiber T U weight epsilon).card =
      (retainedPairTubeFamily fiber T U).card
  endpoint_distinct : EndpointValuesDistinct
    (perturbedRetainedTubeFamily fiber T U weight epsilon)
    (fun V => actualTubeGraph V f) A B
  no_tangential_intersections : NoTangentialGraphIntersections
    (perturbedRetainedTubeFamily fiber T U weight epsilon)
    (fun V => actualTubeGraph V f)
    (fun V => actualTubeGraphFirst V f f1) A B
  data : forall i, i ∈ fiber -> PairLocalActualLensRectangleData
    (perturbedRetainedFirstTube weight epsilon T i)
    (perturbedRetainedSecondTube weight epsilon U i)
    f (sourceRectangles i) A B delta localScale lambda1
  unordered_pair_injective : RetainedUnorderedPairInjective fiber
    (perturbedRetainedFirstTube weight epsilon T)
    (perturbedRetainedSecondTube weight epsilon U)
  endpointInterface : RetainedPairLocalEndpointInterface fiber
    (perturbedRetainedFirstTube weight epsilon T)
    (perturbedRetainedSecondTube weight epsilon U)
    sourceRectangles f A B delta localScale lambda1
  items_card : endpointInterface.items.card = fiber.card
  common_c : forall V,
    V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon -> forall W,
    W ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
      tubeGraphC V = tubeGraphC W
  coefficient_pos : forall V,
    V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon -> forall W,
    W ∈ perturbedRetainedTubeFamily fiber T U weight epsilon -> V ≠ W ->
      0 < tubePairCoefficientDistance V W
  items_pairwise : Set.Pairwise
    (endpointInterface.items : Set
      (FirstGenerationCurvePair
        (retainedPairTubeFamily fiber (perturbedRetainedFirstTube weight epsilon T) (perturbedRetainedSecondTube weight epsilon U))))
    (fun p q => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
      domain center (endpointInterface.rectangles p)
        (endpointInterface.rectangles q) delta localScale referenceScale comparisonLambda))

/-- Canonically extend the lossless retained-index equivalence to a total
endpoint interface while transporting pairwise incomparability to its
literal item finset. -/
theorem exists_total_retainedPairLocalEndpointInterface_with_pairwiseAtScales
    {alpha : Type*} {radius : NNReal} [DecidableEq alpha]
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (f : Real -> Real) (center : C2GraphRectangle) {domain : Set Real}
    (A B delta localScale referenceScale lambda0 comparisonLambda : Real)
    (hfiber : fiber.Nonempty)
    (hpairNe : forall i, i ∈ fiber -> T i ≠ U i)
    (hpairInjective : RetainedUnorderedPairInjective fiber T U)
    (D : forall i, i ∈ fiber -> PairLocalActualLensRectangleData
      (T i) (U i) f (sourceRectangles i) A B delta localScale lambda0)
    (hpairwise : Set.Pairwise (fiber : Set alpha)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (sourceRectangles i) (sourceRectangles j)
          delta localScale referenceScale comparisonLambda))) :
    ∃ E : RetainedPairLocalEndpointInterface fiber T U sourceRectangles
        f A B delta localScale lambda0,
      Set.Pairwise
        (E.items : Set (FirstGenerationCurvePair
          (retainedPairTubeFamily fiber T U)))
        (fun p q => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
          domain center (E.rectangles p) (E.rectangles q)
            delta localScale referenceScale comparisonLambda)) := by
  let items := retainedFirstGenerationCurvePairItems fiber T U
    hpairNe hpairInjective
  let indexEquiv := retainedIndexEquivEndpointItems fiber T U
    hpairNe hpairInjective
  let sourceIndex : {p // p ∈ items} -> {i // i ∈ fiber} :=
    indexEquiv.symm
  let firstTube : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U) -> Tube radius := fun p =>
    if hp : p ∈ items then T (sourceIndex ⟨p, hp⟩).1
    else (firstGenerationCurvePairOutFirst p).1
  let secondTube : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U) -> Tube radius := fun p =>
    if hp : p ∈ items then U (sourceIndex ⟨p, hp⟩).1
    else (firstGenerationCurvePairOutSecond p).1
  let rectangles : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U) -> C2GraphRectangle := fun p =>
    if hp : p ∈ items then sourceRectangles (sourceIndex ⟨p, hp⟩).1
    else sourceRectangles hfiber.choose
  have hfirstMem : forall p, firstTube p ∈
      retainedPairTubeFamily fiber T U := by
    intro p
    by_cases hp : p ∈ items
    · simpa only [firstTube, dif_pos hp] using
        retainedPair_first_mem fiber T U
          (sourceIndex ⟨p, hp⟩).1 (sourceIndex ⟨p, hp⟩).2
    · simpa only [firstTube, dif_neg hp] using
        (firstGenerationCurvePairOutFirst p).2
  have hsecondMem : forall p, secondTube p ∈
      retainedPairTubeFamily fiber T U := by
    intro p
    by_cases hp : p ∈ items
    · simpa only [secondTube, dif_pos hp] using
        retainedPair_second_mem fiber T U
          (sourceIndex ⟨p, hp⟩).1 (sourceIndex ⟨p, hp⟩).2
    · simpa only [secondTube, dif_neg hp] using
        (firstGenerationCurvePairOutSecond p).2
  have hpairEq : forall p : FirstGenerationCurvePair
      (retainedPairTubeFamily fiber T U), p.1 =
      s(⟨firstTube p, hfirstMem p⟩, ⟨secondTube p, hsecondMem p⟩) := by
    intro p
    by_cases hp : p ∈ items
    · let i := sourceIndex ⟨p, hp⟩
      have hE : indexEquiv i = ⟨p, hp⟩ :=
        indexEquiv.apply_symm_apply ⟨p, hp⟩
      have hvalue : (indexEquiv i).1 = p := congrArg Subtype.val hE
      have hfirstCurve :
          (⟨firstTube p, hfirstMem p⟩ : FirstGenerationCurve
            (retainedPairTubeFamily fiber T U)) =
            retainedPairFirstCurve fiber T U i := by
        apply Subtype.ext
        simp only [firstTube, dif_pos hp, retainedPairFirstCurve, i]
      have hsecondCurve :
          (⟨secondTube p, hsecondMem p⟩ : FirstGenerationCurve
            (retainedPairTubeFamily fiber T U)) =
            retainedPairSecondCurve fiber T U i := by
        apply Subtype.ext
        simp only [secondTube, dif_pos hp, retainedPairSecondCurve, i]
      rw [hfirstCurve, hsecondCurve, ← hvalue]
      change (indexEquiv i).1.1 =
        (retainedFirstGenerationCurvePair fiber T U hpairNe i).1
      simp only [indexEquiv, retainedIndexEquivEndpointItems]
      rfl
    · simpa only [firstTube, secondTube, dif_neg hp] using
        firstGenerationCurvePair_eq_out p
  have hdata : forall p, p ∈ items -> PairLocalActualLensRectangleData
      (firstTube p) (secondTube p) f (rectangles p)
        A B delta localScale lambda0 := by
    intro p hp
    simpa only [firstTube, secondTube, rectangles, dif_pos hp] using
      D (sourceIndex ⟨p, hp⟩).1 (sourceIndex ⟨p, hp⟩).2
  let endpoint : RetainedPairLocalEndpointInterface fiber T U
      sourceRectangles f A B delta localScale lambda0 := {
    items := items
    firstTube := firstTube
    secondTube := secondTube
    rectangles := rectangles
    first_mem := hfirstMem
    second_mem := hsecondMem
    pair_eq := hpairEq
    data := hdata
    items_card := retainedFirstGenerationCurvePairItems_card fiber T U
      hpairNe hpairInjective
  }
  have hitemsPairwiseRaw : Set.Pairwise
      (items : Set (FirstGenerationCurvePair
        (retainedPairTubeFamily fiber T U)))
      (fun p q => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (rectangles p) (rectangles q)
          delta localScale referenceScale comparisonLambda)) := by
    intro p hp q hq hpq
    change p ∈ items at hp
    change q ∈ items at hq
    let ip := sourceIndex ⟨p, hp⟩
    let iq := sourceIndex ⟨q, hq⟩
    have hij : ip.1 ≠ iq.1 := by
      intro hijValue
      have hijSubtype : ip = iq := Subtype.ext hijValue
      have hpqSubtype : (⟨p, hp⟩ : {x // x ∈ items}) = ⟨q, hq⟩ :=
        indexEquiv.symm.injective hijSubtype
      exact hpq (congrArg Subtype.val hpqSubtype)
    have hsource := hpairwise ip.2 iq.2 hij
    have hpRect : rectangles p = sourceRectangles ip.1 := by
      dsimp only [ip]
      simp only [rectangles, dif_pos hp]
    have hqRect : rectangles q = sourceRectangles iq.1 := by
      dsimp only [iq]
      simp only [rectangles, dif_pos hq]
    simpa only [hpRect, hqRect] using hsource
  refine ⟨endpoint, ?_⟩
  simpa only [endpoint] using hitemsPairwiseRaw

/-- Starting from the strengthened three-shift output, choose one finite
general-position perturbation, rerun every exact-root producer, prove
unordered-pair injectivity from source pairwise incomparability, and build
the lossless total endpoint interface. -/
theorem exists_perturbedRetainedPairEndpointAssemblyAtScales_of_perturbationReady
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (hfiber : fiber.Nonempty)
    (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (weight : Tube radius -> Real) (f f1 f2 : Real -> Real)
    (center : C2GraphRectangle) {domain : Set Real}
    {A B delta localScale referenceScale lambda0 lambda1 comparisonLambda
      externalTolerance : Real}
    (hexternalTolerance : 0 < externalTolerance)
    (hAB : A < B) (hdelta : 0 < delta) (ht : 0 < localScale)
    (hlambda1 : 1 <= lambda1)
    (hwidth : (1 / 2 : Real) <= B - A)
    (P : forall i, i ∈ fiber ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T i) (U i) f (sourceRectangles i)
          A B delta localScale lambda0 lambda1)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hsmallScale : prop41TangencyScaleFactor (4 * lambda1) * delta <
      localScale / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hf2Continuous : ContinuousOn f2 (Icc A B))
    (hcommonC : forall V, V ∈ retainedPairTubeFamily fiber T U -> forall W,
      W ∈ retainedPairTubeFamily fiber T U -> tubeGraphC V = tubeGraphC W)
    (hweight : Set.InjOn weight
      (retainedPairTubeFamily fiber T U : Set (Tube radius)))
    (hcritical : forall V,
      V ∈ retainedPairTubeFamily fiber T U -> forall W,
      W ∈ retainedPairTubeFamily fiber T U -> V ≠ W ->
        (criticalHeightDifferenceSet
          (fun X => actualTubeGraph X f)
          (fun X => actualTubeGraphFirst X f f1) A B V W).Finite)
    (henlarge : 2 * lambda1 * delta <= comparisonLambda * delta)
    (hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda1) delta localScale <=
      Real.sqrt (comparisonLambda * delta / localScale))
    (hreference : forall epsilon, 0 < epsilon ->
      epsilon < externalTolerance -> forall V,
      V ∈ perturbedRetainedTubeFamily fiber T U weight epsilon ->
        InPointwiseC2BallOn domain center
          (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv
            A B hAB.le) (3 * referenceScale))
    (hpairwise : Set.Pairwise (fiber : Set alpha)
      (fun i j => Not (compactC2SymmetricGraphLambdaComparableOnAtScales
        domain center (sourceRectangles i) (sourceRectangles j)
          delta localScale referenceScale comparisonLambda))) :
    Nonempty (PerturbedRetainedPairEndpointAssemblyAtScales fiber T U
      sourceRectangles weight f f1 center domain
        A B delta localScale referenceScale lambda1 comparisonLambda externalTolerance) := by
  obtain ⟨epsilon, hepsilonPos, hepsilonExternal, hinjective, hcard,
      hA2, hA3, hdataNonempty⟩ :=
    exists_small_positive_actualTubeGeneralPosition_and_pairLocalData_of_perturbationReady
      fiber hfiber T U sourceRectangles weight f f1 f2
      hexternalTolerance ht P (fun z _ => hfDeriv z)
      (fun z _ => hf1Deriv z) hparameter hft hf1Lower hf1Upper hf2
      hweight hcritical
  let D : forall i, i ∈ fiber -> PairLocalActualLensRectangleData
      (perturbedRetainedFirstTube weight epsilon T i)
      (perturbedRetainedSecondTube weight epsilon U i)
      f (sourceRectangles i) A B delta localScale lambda1 :=
    Classical.choice hdataNonempty
  have hfamilyEq :=
    perturbedRetainedTubeFamily_eq_individuallyTracePerturbedTubeFamily
      fiber T U weight epsilon
  have hcard' :
      (perturbedRetainedTubeFamily fiber T U weight epsilon).card =
        (retainedPairTubeFamily fiber T U).card := by
    rw [hfamilyEq]
    exact hcard
  have hA2' : EndpointValuesDistinct
      (perturbedRetainedTubeFamily fiber T U weight epsilon)
      (fun V => actualTubeGraph V f) A B := by
    rw [hfamilyEq]
    exact hA2
  have hA3' : NoTangentialGraphIntersections
      (perturbedRetainedTubeFamily fiber T U weight epsilon)
      (fun V => actualTubeGraph V f)
      (fun V => actualTubeGraphFirst V f f1) A B := by
    rw [hfamilyEq]
    exact hA3
  have hcommonC' := perturbedRetainedTubeFamily_commonC
    fiber T U weight epsilon hcommonC
  have hcoefficient' :=
    tubePairCoefficientDistance_pos_of_endpointDistinct_commonC
      (perturbedRetainedTubeFamily fiber T U weight epsilon)
      f A B hA2' hcommonC'
  have hpairInjective : RetainedUnorderedPairInjective fiber
      (perturbedRetainedFirstTube weight epsilon T)
      (perturbedRetainedSecondTube weight epsilon U) := by
    exact retainedUnorderedPairInjective_of_pairwise_incomparable
      fiber (perturbedRetainedFirstTube weight epsilon T)
      (perturbedRetainedSecondTube weight epsilon U)
      f f1 f2 center sourceRectangles hAB.le hdelta ht hlambda1 hwidth
      hfDeriv hf1Deriv hsmallScale hparameter hft hf1Lower hf1Upper hf2
      hf2Continuous D henlarge hscale
      (fun i hi => hreference epsilon hepsilonPos hepsilonExternal
        (perturbedRetainedFirstTube weight epsilon T i)
        (by
          simpa only [perturbedRetainedTubeFamily] using
            retainedPair_first_mem fiber
              (perturbedRetainedFirstTube weight epsilon T)
              (perturbedRetainedSecondTube weight epsilon U) i hi))
      hpairwise
  have hpairNe : forall i, i ∈ fiber ->
      perturbedRetainedFirstTube weight epsilon T i ≠
        perturbedRetainedSecondTube weight epsilon U i := by
    intro i hi hTU
    have hlower := (D i hi).coefficient_lower
    rw [hTU] at hlower
    have hzero : tubePairCoefficientDistance
        (perturbedRetainedSecondTube weight epsilon U i)
        (perturbedRetainedSecondTube weight epsilon U i) = 0 := by
      simp [tubePairCoefficientDistance, tubePairDeltaA,
        tubePairDeltaB, tubePairDeltaD, coefficientDistance]
    rw [hzero] at hlower
    exact (not_lt_of_ge hlower) ht
  obtain ⟨endpoint, hitemsPairwise⟩ :=
    exists_total_retainedPairLocalEndpointInterface_with_pairwiseAtScales
      fiber (perturbedRetainedFirstTube weight epsilon T)
      (perturbedRetainedSecondTube weight epsilon U)
      sourceRectangles f center A B delta localScale referenceScale lambda1 comparisonLambda
      hfiber hpairNe hpairInjective D hpairwise
  exact ⟨{
    fiber_nonempty := hfiber
    epsilon := epsilon
    epsilon_pos := hepsilonPos
    epsilon_lt_external := hepsilonExternal
    perturb_injective := hinjective
    family_card_eq := hcard'
    endpoint_distinct := hA2'
    no_tangential_intersections := hA3'
    data := D
    unordered_pair_injective := hpairInjective
    endpointInterface := endpoint
    items_card := endpoint.items_card
    common_c := hcommonC'
    coefficient_pos := hcoefficient'
    items_pairwise := hitemsPairwise
  }⟩

/-- The assembled endpoint package supplies every family-, item-, and
pair-local argument of the explicit on-items selected-lens counter.  The
lossless item cardinality rewrites its conclusion back to the retained
source fiber. -/
theorem pairLocalActualSelectedLens_card_le_explicitAtScales_global_of_endpointAssembly
    {alpha : Type*} [DecidableEq alpha] {radius : NNReal}
    (fiber : Finset alpha) (T U : alpha -> Tube radius)
    (sourceRectangles : alpha -> C2GraphRectangle)
    (weight : Tube radius -> Real) (f f1 f2 : Real -> Real)
    (center : C2GraphRectangle) {domain : Set Real}
    {A B delta localScale referenceScale lambda1 comparisonLambda externalTolerance : Real}
    (S : PerturbedRetainedPairEndpointAssemblyAtScales fiber T U
      sourceRectangles weight f f1 center domain
        A B delta localScale referenceScale lambda1 comparisonLambda externalTolerance)
    (hAB : A < B) (M : Real)
    (_hdelta : 0 < delta) (_ht : 0 < localScale) (_hlambda1 : 1 <= lambda1)
    (_hwidth : (1 / 2 : Real) <= B - A)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (_hsmallScale : prop41TangencyScaleFactor (4 * lambda1) * delta <
      localScale / 1200)
    (_hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (_hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (_hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (_hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (_hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (_hf2Continuous : ContinuousOn f2 (Icc A B))
    (hgraphBound : forall V,
      V ∈ perturbedRetainedTubeFamily fiber T U weight S.epsilon ->
        forall theta, theta ∈ Icc A B -> |actualTubeGraph V f theta| <= M)
    (_henlarge : 2 * lambda1 * delta <= comparisonLambda * delta)
    (_hscale : 4 * prop41ActualPairLocalizationRadius
        (4 * lambda1) delta localScale <=
      Real.sqrt (comparisonLambda * delta / localScale))
    (hreference : forall V,
      V ∈ perturbedRetainedTubeFamily fiber T U weight S.epsilon ->
        InPointwiseC2BallOn domain center
          (pairLocalTubeReference V f f1 f2 hfDeriv hf1Deriv
            A B hAB.le) (3 * referenceScale))
    (hmoonCore :
      let curves :=
        perturbedRetainedTubeFamily fiber T U weight S.epsilon
      let E := S.endpointInterface
      forall hpair : forall p : FirstGenerationCurvePair curves, p.1 =
        s(pairLocalActualItemSelectedFirstCurve E.firstTube E.first_mem p,
          pairLocalActualItemSelectedSecondCurve E.secondTube E.second_mem p),
      forall depth : FirstGenerationCurve curves -> Real,
        PairLocalActualSelectedLensTwoScaleMoonCore
          curves E.items E.firstTube E.secondTube E.first_mem E.second_mem
            hpair E.rectangles f f1 f2 A B M depth center domain delta
              localScale referenceScale lambda1 comparisonLambda E.data
                hAB.le hfDeriv hf1Deriv) :
    (fiber.card : Real) <=
      ((perturbedRetainedTubeFamily fiber T U weight S.epsilon).card : Real) +
      3 * (16 *
          (canonicalDepth (FirstGenerationCurve
            (perturbedRetainedTubeFamily fiber T U weight S.epsilon)) : Real) *
          ((perturbedRetainedTubeFamily fiber T U weight S.epsilon).card : Real) *
          Real.sqrt
            ((perturbedRetainedTubeFamily fiber T U weight S.epsilon).card : Real) +
        105 *
          ((perturbedRetainedTubeFamily fiber T U weight S.epsilon).card : Real) *
          Real.sqrt
            ((perturbedRetainedTubeFamily fiber T U weight S.epsilon).card : Real)) := by
  obtain ⟨i0, hi0⟩ := S.fiber_nonempty
  let _ : Nonempty (FirstGenerationCurve
      (perturbedRetainedTubeFamily fiber T U weight S.epsilon)) :=
    ⟨⟨perturbedRetainedFirstTube weight S.epsilon T i0, by
      simpa only [perturbedRetainedTubeFamily] using
        retainedPair_first_mem fiber
          (perturbedRetainedFirstTube weight S.epsilon T)
          (perturbedRetainedSecondTube weight S.epsilon U) i0 hi0⟩⟩
  let E := S.endpointInterface
  have hpair : forall p, p.1 =
      s(pairLocalActualItemSelectedFirstCurve E.firstTube E.first_mem p,
        pairLocalActualItemSelectedSecondCurve E.secondTube E.second_mem p) := by
    intro p
    simpa only [pairLocalActualItemSelectedFirstCurve,
      pairLocalActualItemSelectedSecondCurve] using E.pair_eq p
  have hbound :=
    pairLocalActualSelectedLens_card_le_explicit_global_onItems_of_twoScaleMoonCore
      (perturbedRetainedTubeFamily fiber T U weight S.epsilon)
      E.items E.firstTube E.secondTube E.first_mem E.second_mem hpair
      E.rectangles f f1 f2 hAB M center E.data hfDeriv hf1Deriv
      hgraphBound hreference S.items_pairwise (hmoonCore hpair)
  have hitemsCast : (E.items.card : Real) = (fiber.card : Real) := by
    exact congrArg (fun n : Nat => (n : Real)) S.items_card
  exact hitemsCast.symm.trans_le hbound

#print axioms perturbedRetainedTubeFamily_eq_individuallyTracePerturbedTubeFamily
#print axioms perturbedRetainedTubeFamily_commonC
#print axioms tubePairCoefficientDistance_pos_of_endpointDistinct_commonC
#print axioms exists_total_retainedPairLocalEndpointInterface_with_pairwiseAtScales
#print axioms exists_perturbedRetainedPairEndpointAssemblyAtScales_of_perturbationReady
#print axioms pairLocalActualSelectedLens_card_le_explicitAtScales_global_of_endpointAssembly
end

end FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1
