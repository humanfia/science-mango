import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleConsumerRepoV2V1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleSourcePairwiseV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleOutcomeRepoV2V1

open Set
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualTubeConstantShiftV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
open FamilyStickyCinematicL32Lemma55SymmetricRectangleComparabilityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
open FamilyStickyCinematicL32Prop41TangencyProductToScaleV1
open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41ActualPairRectangleLensLocalizationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41ActualRectangularSkirtPairEncCardCleanV1
open FamilyStickyCinematicL32Prop41ActualTubeGraphCinematicDerivativeV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingEndpointConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1PaperFineThreeShiftScaleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineUniformPackageV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedConsumerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleSourcePairwiseV1
open FamilyStickyCinematicL32Prop41SelectedSubfamilyTwoScaleConsumerRepoV2V1
open FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionEndpointAssemblyTwoScaleRepoV2V1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41MarcusTardosCanonicalDepthCountingV1
open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
open FamilyStickyCinematicL32Prop41SampledLensPaperShapeNumericsV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

/-!
# Actual selected paper-fine two-scale outcome and sampling endpoint

All tangency, localization and graph comparison data stay at `pairScale`.
Only the common-reference C2 ball uses the independent `referenceScale`.
The global source hypothesis is reference-free, so it honestly supplies the
two-scale compact incomparability relation for every reference radius.
-/

/-- Actual paper-fine specialization of the RepoV2 two-scale selected
counting package, with source pairwise data left external. -/
abbrev ActualSharedGlobalPaperFineSelectedTwoScaleCountingNoSourcePairwisePackage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale depth : Real)
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale) :=
  SelectedSubfamilyFiniteGeneralPositionTwoScaleCountingNoSourcePairwisePackage
    P.selected
    (actualSharedGlobalPaperFineSelectedLeftTube fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega labelAt
        f outerA outerB globalDelta tGlobal pairScale P)
    (actualSharedGlobalPaperFineSelectedRightTube fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega labelAt
        f outerA outerB globalDelta tGlobal pairScale P)
    (actualSharedGlobalPaperFineSelectedRectangle fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega labelAt
        f outerA outerB globalDelta tGlobal pairScale P)
    f f1 f2 outerA outerB
    (actualY1PaperFineChoiceLocalDelta
      (radius : Real) globalDelta tGlobal pairScale)
    pairScale referenceScale
    (2 * actualY1PaperFineChoiceLambda
      (radius : Real) globalDelta tGlobal pairScale)
    depth center domain comparisonLambda hfDeriv hf1Deriv

/-- Outcome-local producer and all residual two-scale geometry.  Source
pairwise data is deliberately absent: one global fine-label statement will
be pulled back to every outcome. -/
structure ActualSharedGlobalPaperFineSelectedTwoScaleOutcomeNoSourcePairwisePackage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale depth : Real)
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z) where
  labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega ->
      fineLabel
  uniform : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale
  counting :
    ActualSharedGlobalPaperFineSelectedTwoScaleCountingNoSourcePairwisePackage
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
          tGlobal pairScale referenceScale depth center domain comparisonLambda
            hfDeriv hf1Deriv uniform

/-- The actual two-scale selected family gives the same factor-three
certificate as the old consumer, now with an independent reference scale.
The only global source premise is reference-free fine-label
incomparability. -/
theorem actualSharedGlobalSurvivorPaperFineSelectedLensCertificateAtScales_of_uniformPackage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale depth : Real)
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (G :
      ActualSharedGlobalPaperFineSelectedTwoScaleCountingNoSourcePairwisePackage
        fine physical globalScale globalCenter D keep rectangles left right
          ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
            tGlobal pairScale referenceScale depth center domain comparisonLambda
              hfDeriv hf1Deriv P)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (symmetricGraphLambdaComparable
        (D.fineRectangleAt r).rectangle (D.fineRectangleAt s).rectangle
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale comparisonLambda))) :
    ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale P depth := by
  let T := actualSharedGlobalPaperFineSelectedLeftTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let U := actualSharedGlobalPaperFineSelectedRightTube fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let source := actualSharedGlobalPaperFineSelectedRectangle fine physical
    globalScale globalCenter D keep rectangles left right ballRadius mu nu
      omega labelAt f outerA outerB globalDelta tGlobal pairScale P
  let localDelta := actualY1PaperFineChoiceLocalDelta
    (radius : Real) globalDelta tGlobal pairScale
  have hdata : forall a, a ∈ P.selected ->
      PerturbationReadyPairLocalActualLensRectangleData
        (T a) (U a) f (source a) outerA outerB localDelta pairScale
          (actualY1PaperFineChoiceLambda
            (radius : Real) globalDelta tGlobal pairScale)
          (2 * actualY1PaperFineChoiceLambda
            (radius : Real) globalDelta tGlobal pairScale) := by
    intro a ha
    simpa only [T, U, source, localDelta,
      actualSharedGlobalPaperFineSelectedLeftTube,
      actualSharedGlobalPaperFineSelectedRightTube,
      actualSharedGlobalPaperFineSelectedRectangle] using P.data a ha
  have hsource : Set.Pairwise (P.selected : Set _)
      (fun i j => Not
        (FamilyStickyCinematicL32Prop41SelectedTwoScaleCountingAdapterV1.compactC2SymmetricGraphLambdaComparableOnAtScales
          domain center (source i) (source j) localDelta pairScale
            referenceScale comparisonLambda)) := by
    simpa only [source, localDelta] using
      (actualSharedGlobalPaperFineSelected_sourcePairwiseAtScales_of_referenceFreeFineLabelsPairwise
        fine physical globalScale globalCenter D keep rectangles left right
          ballRadius mu nu omega labelAt f outerA outerB globalDelta tGlobal
            pairScale P domain center localDelta pairScale referenceScale
              comparisonLambda hfineLabels)
  have hselected :=
    selectedSubfamily_card_le_sampledLensBoundAtScales_of_perturbationReady
      P.selected P.selected_nonempty T U source f f1 f2 center domain
        comparisonLambda hfDeriv hf1Deriv hdata G hsource
  have hretention :
      ((actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega).card : Real) <=
        3 * (P.selected.card : Real) := by
    exact_mod_cast P.cardinal_retention
  unfold ActualSharedGlobalSurvivorPaperFineSelectedLensCertificate
  rw [← actualSharedGlobalSurvivorFiber_card fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega]
  calc
    ((actualSharedGlobalSurvivorFiber fine physical globalScale globalCenter
        D keep rectangles left right ballRadius mu nu omega).card : Real) <=
        3 * (P.selected.card : Real) := hretention
    _ <= 3 * sampledLensBound depth
        ((actualSharedGlobalPaperFineSelectedRetainedTubeFamily fine physical
          globalScale globalCenter D keep rectangles left right ballRadius
            mu nu omega labelAt f outerA outerB globalDelta tGlobal pairScale
              P).card : Real) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [actualSharedGlobalPaperFineSelectedRetainedTubeFamily,
        T, U] using hselected

/-- Per-outcome load form of the actual two-scale selected estimate. -/
theorem actualSharedGlobalSurvivor_card_le_three_mul_sampledLensBound_loadAtScales_of_paperFineUniformPackage
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu))
    (labelAt : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep rectangles left right ballRadius mu nu omega ->
        fineLabel)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale depth : Real)
    (hdepth : 0 <= depth)
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (P : ActualSharedGlobalSurvivorPaperFineUniformPackage fine physical
      globalScale globalCenter D keep rectangles left right ballRadius mu nu
        omega labelAt f outerA outerB globalDelta tGlobal pairScale)
    (G :
      ActualSharedGlobalPaperFineSelectedTwoScaleCountingNoSourcePairwisePackage
        fine physical globalScale globalCenter D keep rectangles left right
          ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
            tGlobal pairScale referenceScale depth center domain comparisonLambda
              hfDeriv hf1Deriv P)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (symmetricGraphLambdaComparable
        (D.fineRectangleAt r).rectangle (D.fineRectangleAt s).rectangle
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale comparisonLambda))) :
    ((twoSidedZeroColorSurvivors mu nu
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left)
      (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right) omega).card : Real) <=
      3 * sampledLensBound depth (twoSidedZeroColorLoad mu nu omega) := by
  let C :=
    actualSharedGlobalSurvivorPaperFineSelectedLensCertificateAtScales_of_uniformPackage
      fine physical globalScale globalCenter D keep rectangles left right
        ballRadius mu nu omega labelAt f f1 f2 outerA outerB globalDelta
          tGlobal pairScale referenceScale depth center domain comparisonLambda
            hfDeriv hf1Deriv P G hfineLabels
  exact C.card_le_three_mul_sampledLensBound_load fine physical globalScale
    globalCenter D keep rectangles left right ballRadius mu nu omega labelAt f
      outerA outerB globalDelta tGlobal pairScale P depth hdepth

/-- Actual RepoV2 two-scale paper-fine sampling endpoint.  Every nonempty
outcome provides its producer and residual geometry; one global reference-free
fine-label hypothesis supplies source pairwise data to all outcomes. -/
theorem actualSharedGlobalPaperFineSelected_rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteenAtScales
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (rectangles : Finset C2GraphRectangle)
    (left right : Tube radius) (ballRadius : Real)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (hleft : forall R : rectangles,
      mu <= (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius left R).card)
    (hright : forall R : rectangles,
      nu <= (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
        globalCenter D keep rectangles ballRadius right R).card)
    (f f1 f2 : Real -> Real)
    (outerA outerB globalDelta tGlobal pairScale referenceScale depth : Real)
    (hdepth : 0 <= depth)
    (center : C2GraphRectangle) (domain : Set Real)
    (comparisonLambda : Real)
    (hfDeriv : forall z, HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, HasDerivAt f1 (f2 z) z)
    (hgeometry : forall omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu),
      (twoSidedZeroColorSurvivors mu nu
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius left)
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius right) omega).Nonempty ->
      ActualSharedGlobalPaperFineSelectedTwoScaleOutcomeNoSourcePairwisePackage
        fine physical globalScale globalCenter D keep rectangles left right
          ballRadius mu nu omega f f1 f2 outerA outerB globalDelta tGlobal
            pairScale referenceScale depth center domain comparisonLambda
              hfDeriv hf1Deriv)
    (hfineLabels : Set.Pairwise (Set.univ : Set fineLabel)
      (fun r s => Not (symmetricGraphLambdaComparable
        (D.fineRectangleAt r).rectangle (D.fineRectangleAt s).rectangle
          (actualY1PaperFineChoiceLocalDelta
            (radius : Real) globalDelta tGlobal pairScale)
          pairScale comparisonLambda))) :
    let ambient :=
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    let load := 7 * ((ambient.card : Real) / (mu : Real) +
      (ambient.card : Real) / (nu : Real))
    ((rectangles.card : Nat) : Real) <=
      8 * (316 + 48 * (3 * depth + 14)) * load * Real.sqrt load := by
  dsimp only
  let leftNeighbors :=
    actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius left
  let rightNeighbors :=
    actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep rectangles ballRadius right
  have hsampledLens : forall omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin mu) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin nu),
      ((twoSidedZeroColorSurvivors mu nu leftNeighbors rightNeighbors
        omega).card : Real) <=
        3 * sampledLensBound depth (twoSidedZeroColorLoad mu nu omega) := by
    intro omega
    by_cases hsurvivor : (twoSidedZeroColorSurvivors mu nu leftNeighbors
        rightNeighbors omega).Nonempty
    · let O := hgeometry omega hsurvivor
      exact
        actualSharedGlobalSurvivor_card_le_three_mul_sampledLensBound_loadAtScales_of_paperFineUniformPackage
          fine physical globalScale globalCenter D keep rectangles left right
            ballRadius mu nu omega O.labelAt f f1 f2 outerA outerB globalDelta
              tGlobal pairScale referenceScale depth hdepth center domain
                comparisonLambda hfDeriv hf1Deriv O.uniform O.counting
                  hfineLabels
    · rw [Finset.not_nonempty_iff_eq_empty.mp hsurvivor]
      norm_num only [Finset.card_empty, Nat.cast_zero]
      have hload : 0 <= twoSidedZeroColorLoad mu nu omega :=
        twoSidedZeroColorLoad_nonneg mu nu omega
      unfold sampledLensBound
      positivity
  simpa only [leftNeighbors, rightNeighbors, Fintype.card_coe] using
    (rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteen_of_twoSidedSampling_factorThree_automaticBudget
      mu nu leftNeighbors rightNeighbors hleft hright depth hdepth
        hsampledLens)

#print axioms ActualSharedGlobalPaperFineSelectedTwoScaleCountingNoSourcePairwisePackage
#print axioms ActualSharedGlobalPaperFineSelectedTwoScaleOutcomeNoSourcePairwisePackage
#print axioms actualSharedGlobalSurvivorPaperFineSelectedLensCertificateAtScales_of_uniformPackage
#print axioms actualSharedGlobalSurvivor_card_le_three_mul_sampledLensBound_loadAtScales_of_paperFineUniformPackage
#print axioms actualSharedGlobalPaperFineSelected_rectangleCard_le_sampledLensPaperShape_threeDepth_add_fourteenAtScales

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedTwoScaleOutcomeRepoV2V1
