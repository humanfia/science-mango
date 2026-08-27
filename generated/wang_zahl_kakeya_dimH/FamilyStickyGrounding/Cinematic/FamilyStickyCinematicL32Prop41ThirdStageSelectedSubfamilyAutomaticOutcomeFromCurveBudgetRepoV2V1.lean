import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set

namespace FamilyStickyCinematicL32Prop41ThirdStageSelectedSubfamilyAutomaticOutcomeFromCurveBudgetRepoV2V1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteNestedValueFibresThirdStageAtScalesV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Lemma316AutomaticCompactC2GreedySelectionTwoCenterV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedBasicNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleAutomaticGeometryRepoV2V1
open FamilyStickyCinematicL32Prop41ActualY1SharpFineScaleTangencyV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleAutomaticOutcomeFromCurveBudgetRepoV2V1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41SharpCommonCReferenceV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1

noncomputable section

universe u

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

/-!
# Third-stage selected-subfamily endpoint from a finite curve budget

This adapter consumes the output of the honest cross-code weighted greedy
stage directly.  Its carrier is completely generic, so it applies in
particular to the sigma-tagged code candidates without erasing their tags.
The only conversion is definitional: the Pairwise field of the third-stage
outcome is exactly the AtScales source Pairwise input of the sampled-lens
selected-subfamily theorem.
-/

/-- A package-free third-stage outcome supplies the final AtScales Pairwise
family required by sampled-lens counting.  The natural curve budget supplies
the logarithmic depth automatically. -/
theorem thirdStageSelected_card_le_sampledLensBoundAtScales_automatic_of_curveBudget
    {candidate : Type u} [DecidableEq candidate] {radius : NNReal}
    (vertices : Finset candidate)
    (T U : candidate -> Tube radius)
    (source : candidate -> C2GraphRectangle)
    (globalCenter : Tube radius) (commonC rho : Real)
    (curveBudget : Nat)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale : Real)
    (weight : candidate -> ENNReal) (thirdPacking : ENNReal)
    (hOuter : outerA <= outerB)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (sharp : ActualY1SharpFineScaleNumerics
      (radius : Real) globalDelta tGlobal (outerB - outerA))
    (hthree : ActualY1PaperFineThreeShiftPairScaleSmallness
      (radius : Real) globalDelta tGlobal pairScale)
    (hcount : ActualY1PaperFineSelectedCountingSmallness
      (radius : Real) globalDelta tGlobal pairScale)
    (hparameter : forall z, z ∈ Icc outerA outerB -> |z| <= 1)
    (hfunction : forall z, z ∈ Icc outerA outerB -> |f z| <= 2)
    (hfirstLower : forall z, z ∈ Icc outerA outerB -> 1 <= |f1 z|)
    (hfirstUpper : forall z, z ∈ Icc outerA outerB -> |f1 z| <= 2)
    (hsecond : forall z, z ∈ Icc outerA outerB -> |f2 z| <= 1 / 100)
    (hsecondContinuous : ContinuousOn f2 (Icc outerA outerB))
    (Q : FiniteThirdStageGreedyOutcome vertices
      (compactC2ComparableAtScales source (Icc outerA outerB)
        (globalCenterFixedCommonCReference globalCenter commonC f f1 f2
          hfDeriv hf1Deriv outerA outerB hOuter)
        (actualY1PaperFineChoiceLocalDelta
          (radius : Real) globalDelta tGlobal pairScale)
        pairScale referenceScale
        (actualY1PaperFineSelectedAutomaticComparisonLambda
          (radius := radius) globalDelta tGlobal pairScale))
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
    (hdata : forall a, a ∈ Q.selected ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T a) (U a) f (source a) outerA outerB
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale
          (actualY1PaperFineChoiceLambda
            (radius : Real) globalDelta tGlobal pairScale)
          (2 * actualY1PaperFineChoiceLambda
            (radius : Real) globalDelta tGlobal pairScale)) :
    (Q.selected.card : Real) <=
      sampledLensBound
        (selectedSubfamilyAutomaticDepthFromCurveBudget curveBudget)
        ((retainedPairTubeFamily Q.selected T U).card : Real) := by
  refine
    selectedSubfamily_card_le_sampledLensBoundAtScales_automatic_of_curveBudget
      Q.selected (Q.selected_nonempty hvertices) T U source globalCenter
      commonC rho curveBudget f f1 f2 outerA outerB globalDelta tGlobal
      pairScale referenceScale hOuter hfDeriv hf1Deriv sharp hthree hcount
      hparameter hfunction hfirstLower hfirstUpper hsecond hsecondContinuous
      hcommon hball hcurveBudget hreferenceMargin hdata ?_
  simpa only [compactC2ComparableAtScales,
    FamilyStickyCinematicL32Prop41TwoScaleComparabilityCoreV1.compactC2SymmetricGraphLambdaComparableOnAtScales,
    FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1.compactC2SymmetricGraphLambdaComparableOnAtScales] using
        Q.selected_pairwise

#print axioms thirdStageSelected_card_le_sampledLensBoundAtScales_automatic_of_curveBudget

end

end FamilyStickyCinematicL32Prop41ThirdStageSelectedSubfamilyAutomaticOutcomeFromCurveBudgetRepoV2V1
