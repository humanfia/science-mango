import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeConcreteSamplingConnectorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeMassBudgetNumericsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeBudgetSampleConnectorV1

open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualCoarseFiberIndexRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeMassBlockProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeMassBudgetNumericsV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeConcreteSamplingConnectorV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

/-!
# Budgeted concrete G-prime sampling endpoint

The exact source-mass budget replaces the residual selected-bucket mass-block
premise.  The common-fibre richness bridge then feeds the finite sampler at
`mu = nu = 1`, producing an actual colouring together with survival, load,
and retained-tube-family estimates.
-/

/-- A concrete bridge outcome augmented by one actual zero-colour sampling
outcome on its full common coarse-rectangle fibre. -/
structure ActualConcreteGPrimeCommonCoarseSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (rectangles : Finset C2GraphRectangle)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) : Prop where
  selection : ActualConcreteGPrimeCommonCoarseSamplingOutcome fine physical
    globalScale globalCenter N D ballRadius bucket keep left right rectangles
  survival :
    ((rectangles.card : Nat) : Real) / 8 <=
      ((twoSidedZeroColorSurvivors 1 1
        (fun R : rectangles =>
          ambientSubtypeRestriction N.family
            (D.coarseCurveMetricBall keep R.1
              projectedTubePairCoefficientDistance ballRadius
                (D.fine.tubes left)))
        (fun R : rectangles =>
          ambientSubtypeRestriction N.family
            (D.coarseCurveMetricBall keep R.1
              projectedTubePairCoefficientDistance ballRadius
                (D.fine.tubes right))) omega).card : Real)
  load : twoSidedZeroColorLoad 1 1 omega <=
    7 * ((N.family.card : Real) / (1 : Real) +
      (N.family.card : Real) / (1 : Real))
  retained_tube_card_le_load :
    ((survivorRetainedPairTubeFamily 1 1
      (fun R : rectangles =>
        ambientSubtypeRestriction N.family
          (D.coarseCurveMetricBall keep R.1
            projectedTubePairCoefficientDistance ballRadius
              (D.fine.tubes left)))
      (fun R : rectangles =>
        ambientSubtypeRestriction N.family
          (D.coarseCurveMetricBall keep R.1
            projectedTubePairCoefficientDistance ballRadius
              (D.fine.tubes right)))
      omega (fun i : N.family => D.fine.tubes i.1)
        (fun i : N.family => D.fine.tubes i.1)).card : Real) <=
      twoSidedZeroColorLoad 1 1 omega

/-- Feed an already selected common-fibre bridge to the finite sampler. -/
theorem exists_actualConcreteGPrimeCommonCoarseSample_of_bridge
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (ballRadius : Real) (bucket : Nat)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (rectangles : Finset C2GraphRectangle)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical globalScale globalCenter)
    (hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseCurveIndexFiber keep R ⊆ N.family)
    (O : ActualConcreteGPrimeCommonCoarseSamplingOutcome fine physical
      globalScale globalCenter N D ballRadius bucket keep left right
        rectangles) :
    exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
      ActualConcreteGPrimeCommonCoarseSampledOutcome fine physical
        globalScale globalCenter N D ballRadius bucket keep left right
          rectangles omega := by
  have hleftCard : forall R, R ∈ rectangles ->
      1 <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius
          (D.fine.tubes left)).card := by
    intro R hR
    have hRcommon : R ∈
        actualGPrimeCommonCoarseRectangles D keep left right := by
      rw [← O.rectangles_eq]
      exact hR
    have hrestricted := O.bridge.left_rich_one ⟨R, hRcommon⟩
    have hsub : D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius
          (D.fine.tubes left) ⊆ N.family := by
      intro i hi
      exact hfiberSubset R hR ((D.mem_coarseCurveMetricBall_iff keep).mp hi).1
    have hrestrictedN : 1 <=
        (ambientSubtypeRestriction N.family
          (D.coarseCurveMetricBall keep R
            projectedTubePairCoefficientDistance ballRadius
              (D.fine.tubes left))).card := by
      simp only [actualSharedGlobalCoarseCurveNeighbors] at hrestricted
      rw [← hfamily] at hrestricted
      exact hrestricted
    rw [ambientSubtypeRestriction_card_eq N.family _ hsub] at hrestrictedN
    exact hrestrictedN
  have hrightCard : forall R, R ∈ rectangles ->
      1 <= (D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius
          (D.fine.tubes right)).card := by
    intro R hR
    have hRcommon : R ∈
        actualGPrimeCommonCoarseRectangles D keep left right := by
      rw [← O.rectangles_eq]
      exact hR
    have hrestricted := O.bridge.right_rich_one ⟨R, hRcommon⟩
    have hsub : D.coarseCurveMetricBall keep R
        projectedTubePairCoefficientDistance ballRadius
          (D.fine.tubes right) ⊆ N.family := by
      intro i hi
      exact hfiberSubset R hR ((D.mem_coarseCurveMetricBall_iff keep).mp hi).1
    have hrestrictedN : 1 <=
        (ambientSubtypeRestriction N.family
          (D.coarseCurveMetricBall keep R
            projectedTubePairCoefficientDistance ballRadius
              (D.fine.tubes right))).card := by
      simp only [actualSharedGlobalCoarseCurveNeighbors] at hrestricted
      rw [← hfamily] at hrestricted
      exact hrestricted
    rw [ambientSubtypeRestriction_card_eq N.family _ hsub] at hrestrictedN
    exact hrestrictedN
  obtain ⟨omega, hsurvival, hload⟩ :=
    exists_actualCoarseFiberIndex_sample_with_eighth_survival_and_sevenfold_load
      N D keep rectangles projectedTubePairCoefficientDistance
        (D.fine.tubes left) (D.fine.tubes right) ballRadius 1 1
        hfiberSubset hleftCard hrightCard
  refine ⟨omega, {
    selection := O
    survival := hsurvival
    load := by simpa only [Nat.cast_one] using hload
    retained_tube_card_le_load := ?_ }⟩
  exact survivorRetainedPairTubeFamily_card_cast_le_load 1 1
    (fun R : rectangles =>
      ambientSubtypeRestriction N.family
        (D.coarseCurveMetricBall keep R.1
          projectedTubePairCoefficientDistance ballRadius
            (D.fine.tubes left)))
    (fun R : rectangles =>
      ambientSubtypeRestriction N.family
        (D.coarseCurveMetricBall keep R.1
          projectedTubePairCoefficientDistance ballRadius
            (D.fine.tubes right)))
    omega (fun i : N.family => D.fine.tubes i.1)
      (fun i : N.family => D.fine.tubes i.1)

/-- End-to-end source-budget endpoint.  The source budget is the weakest
existing producer premise that mechanically implies the selected mass block;
no positivity callback remains after it is supplied. -/
theorem exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSample_of_budget
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (base : Set (Real × Real)) (hbase : MeasurableSet base)
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (globalScale : Real) (globalCenter : Tube radius)
    (ceiling exponent threshold fineT coarseDelta coarseT : Real)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = actualCenteredHalfY1FineCoarseRectangleData base hbase fine
      physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
      globalScale globalCenter ceiling exponent threshold fineT coarseDelta
      coarseT)
    (hgood : D.goodPairs.Nonempty)
    (hradius : 0 < radius) (hradiusSixteen : (radius : Real) <= 16)
    (hexponent : 0 <= exponent) (ballRadius : Real)
    (hradiusBall : (radius : Real) <= ballRadius)
    (hnearRadiusUpper : 10 * ballRadius <= 16) :
    exists N : CanonicalNormNonconcentrationData iota,
      N.family =
          actualGlobalNormIndexFamily fine physical globalScale globalCenter ∧
      (forall i j, N.distance i j =
        projectedTubePairCoefficientDistance
          (D.fine.tubes i) (D.fine.tubes j)) ∧
      ∃ bucket ∈ Finset.range (coarseDegreeBucketLoss D),
        0 < comparableBase bucket ∧
        D.goodPairs.card <= coarseDegreeBucketLoss D *
          (D.retainedGoodPairs
            (coarseDegreeBucketKeep D bucket)).card ∧
        (AutomaticRichRetainedMassBudget D
            (automaticCanonicalRichness N ballRadius)
            (2 * comparableBase bucket) ->
          exists keep : iota -> fineLabel -> Prop,
            exists left right : iota,
              exists rectangles : Finset C2GraphRectangle,
                exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
                  ActualConcreteGPrimeCommonCoarseSampledOutcome fine physical
                    globalScale globalCenter N D ballRadius bucket keep left
                      right rectangles omega) := by
  obtain ⟨N, hfamily, hdistance, bucket, hbucket, hbasePos, hselection,
      hselectedIf⟩ :=
    exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSamplingBridge
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT D hD hgood hradius hradiusSixteen hexponent
      ballRadius hradiusBall hnearRadiusUpper
  refine ⟨N, hfamily, hdistance, bucket, hbucket, hbasePos, hselection, ?_⟩
  intro hbudget
  have hmassBlock : 2 * comparableBase bucket <=
      automaticRichRetainedMassLower D
        (automaticCanonicalRichness N ballRadius)
        (2 * comparableBase bucket) :=
    degreeUpper_le_automaticRichRetainedMassLower_of_budget D
      (automaticCanonicalRichness N ballRadius) (2 * comparableBase bucket)
      hbudget
  obtain ⟨keep, left, right, rectangles, O⟩ := hselectedIf hmassBlock
  have hfiberSubset : forall R, R ∈ rectangles ->
      D.coarseCurveIndexFiber keep R ⊆ N.family := by
    intro R _hR
    rw [hfamily, hD]
    exact actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT keep R
  obtain ⟨omega, hsample⟩ :=
    exists_actualConcreteGPrimeCommonCoarseSample_of_bridge fine physical
      globalScale globalCenter N D ballRadius bucket keep left right rectangles
      hfamily hfiberSubset O
  exact ⟨keep, left, right, rectangles, omega, hsample⟩

#print axioms ActualConcreteGPrimeCommonCoarseSampledOutcome
#print axioms exists_actualConcreteGPrimeCommonCoarseSample_of_bridge
#print axioms exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSample_of_budget

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeBudgetSampleConnectorV1
