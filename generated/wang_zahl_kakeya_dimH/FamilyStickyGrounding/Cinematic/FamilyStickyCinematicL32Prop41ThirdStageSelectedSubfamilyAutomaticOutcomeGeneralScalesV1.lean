import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticGeometryGeneralScalesV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ThirdStageSelectedSubfamilyAutomaticOutcomeFromCurveBudgetRepoV2V1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set

namespace FamilyStickyCinematicL32Prop41ThirdStageSelectedSubfamilyAutomaticOutcomeGeneralScalesV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticGeometryGeneralScalesV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleConsumerRepoV2V1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-- The honest third-stage sampled-lens endpoint at arbitrary already-proved
local and comparison scales. This is the direct consumer of the six-radius
C-normalized lane. -/
theorem thirdStageSelected_card_le_sampledLensBoundAtScales_of_scalars_curveBudget
    {candidate : Type u} [DecidableEq candidate] {radius : NNReal}
    (vertices : Finset candidate)
    (T U : candidate -> Tube radius)
    (source : candidate -> C2GraphRectangle)
    (globalCenter : Tube radius) (commonC rho : Real)
    (curveBudget : Nat)
    (f f1 f2 : Real -> Real)
    (A B delta localScale referenceScale lambda0 lambda1
      comparisonLambda : Real)
    (weight : candidate -> ENNReal) (thirdPacking : ENNReal)
    (hOuter : A <= B)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hintervalStrict : A < B)
    (hdelta : 0 < delta)
    (hlocalScale : 0 < localScale)
    (hlambda1 : 1 <= lambda1)
    (hintervalWidth : (1 / 2 : Real) <= B - A)
    (hsmallScale :
      prop41TangencyScaleFactor (4 * lambda1) * delta <
        localScale / 1200)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hfirstLower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hfirstUpper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hsecondContinuous : ContinuousOn f2 (Icc A B))
    (Q : FiniteThirdStageGreedyOutcome vertices
      (compactC2ComparableAtScales source (Icc A B)
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv A B hOuter)
        delta localScale referenceScale comparisonLambda)
      weight thirdPacking)
    (hvertices : vertices.Nonempty)
    (hcommon : forall V,
      V ∈ retainedPairTubeFamily Q.selected T U ->
        tubeGraphC V = commonC)
    (hball : forall V,
      V ∈ retainedPairTubeFamily Q.selected T U ->
        tubePairCoefficientDistance V globalCenter <= rho)
    (hcurveBudget :
      (retainedPairTubeFamily Q.selected T U).card <= curveBudget)
    (hreferenceMargin :
      max ((401 / 100 : Real) * rho) (2 * rho + 0) <
        3 * referenceScale)
    (hcomparisonEnlarges :
      2 * lambda1 * delta <= comparisonLambda * delta)
    (hlocalization :
      4 * prop41ActualPairLocalizationRadius
          (4 * lambda1) delta localScale <=
        Real.sqrt (comparisonLambda * delta / localScale))
    (hdata : forall a, a ∈ Q.selected ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T a) (U a) f (source a) A B delta localScale lambda0 lambda1) :
    (Q.selected.card : Real) <=
      sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget curveBudget)
        ((retainedPairTubeFamily Q.selected T U).card : Real) := by
  let depth := selectedSubfamilyAutomaticDepthFromCurveBudget curveBudget
  have hdepth :
      (canonicalDepth (FirstGenerationCurve
        (retainedPairTubeFamily Q.selected T U)) : Real) <= depth := by
    simpa only [depth] using
      selectedSubfamily_depth_le_automaticDepthFromCurveBudget
        Q.selected T U curveBudget hcurveBudget
  obtain ⟨G⟩ :=
    exists_selectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage_of_scalars
      Q.selected T U source globalCenter commonC rho f f1 f2 A B delta
        localScale referenceScale lambda1 depth comparisonLambda hOuter
        hfDeriv hf1Deriv hintervalStrict hdelta hlocalScale hlambda1
        hintervalWidth hsmallScale hparameter hfunction hfirstLower
        hfirstUpper hsecond hsecondContinuous hcommon hball hdepth
        hreferenceMargin hcomparisonEnlarges hlocalization
  have hsource : Set.Pairwise (Q.selected : Set candidate)
      (fun a b => Not
        (FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1.compactC2SymmetricGraphLambdaComparableOnAtScales
            (Icc A B)
            (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
              hfDeriv hf1Deriv A B hOuter)
            (source a) (source b) delta localScale referenceScale
              comparisonLambda)) := by
    simpa only [compactC2ComparableAtScales,
      FamilyStickyCinematicL32Prop41TwoScaleComparabilityCoreV1.compactC2SymmetricGraphLambdaComparableOnAtScales,
      FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1.compactC2SymmetricGraphLambdaComparableOnAtScales] using
        Q.selected_pairwise
  simpa only [depth] using
    selectedSubfamily_card_le_sampledLensBoundAtScales_of_perturbationReady
      Q.selected (Q.selected_nonempty hvertices) T U source f f1 f2
      (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
        hfDeriv hf1Deriv A B hOuter)
      (Icc A B) comparisonLambda hfDeriv hf1Deriv hdata G hsource

#print axioms thirdStageSelected_card_le_sampledLensBoundAtScales_of_scalars_curveBudget

end

end FamilyStickyCinematicL32Prop41ThirdStageSelectedSubfamilyAutomaticOutcomeGeneralScalesV1
