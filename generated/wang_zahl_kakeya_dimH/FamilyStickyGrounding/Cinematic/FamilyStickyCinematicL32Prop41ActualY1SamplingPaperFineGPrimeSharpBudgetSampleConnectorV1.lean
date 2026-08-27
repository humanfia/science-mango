import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeSharpE2MassConnectorV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeBudgetSampleConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSharpBudgetSampleConnectorV1

open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41ActualCoarseFiberIndexRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeSharpE2MassConnectorV1
open FamilyStickyCinematicL32Prop41ActualGPrimeSharpPoorMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

/-!
# Concrete G-prime sampling with the sharp poor-rectangle mass

This is the concrete counterpart of the predecessor-sized poor subtraction.
It differs from the earlier connector only in the mass lower bound: poor
rectangles are charged at `nearCap`, while selected rectangles retain the
strict threshold `nearCap + 1`.
-/

/-- A concrete G-prime bridge selected using the exact poor-fibre mass. -/
structure ActualConcreteGPrimeCommonCoarseSharpSamplingOutcome
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
    (rectangles : Finset C2GraphRectangle) : Prop where
  mass_block :
    2 * comparableBase bucket <=
      automaticRichRetainedMassLower D
        (automaticCanonicalNearCap N ballRadius)
        (2 * comparableBase bucket)
  keep_eq : keep = coarseDegreeBucketKeep D bucket
  left_mem : left ∈ N.family
  right_mem : right ∈ N.family
  canonical_separated : canonicalTenRadiusSeparated N ballRadius left right
  coarse_good : D.CoarseGoodPair keep left right
  cross_separated : FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
    (finiteFamilyMetricBall N.family N.distance ballRadius left)
    (finiteFamilyMetricBall N.family N.distance ballRadius right)
  rectangles_eq :
    rectangles = actualGPrimeCommonCoarseRectangles D keep left right
  bridge : ActualGPrimeCommonCoarseSamplingBridge fine physical globalScale
    globalCenter D keep left right ballRadius

/-- The concrete actual-centered-half producer using the sharp mass lower. -/
theorem exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSharpSamplingBridge
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
        (2 * comparableBase bucket <=
            automaticRichRetainedMassLower D
              (automaticCanonicalNearCap N ballRadius)
              (2 * comparableBase bucket) ->
          exists keep : iota -> fineLabel -> Prop,
            exists left right : iota,
              exists rectangles : Finset C2GraphRectangle,
                ActualConcreteGPrimeCommonCoarseSharpSamplingOutcome
                  fine physical globalScale globalCenter N D ballRadius bucket
                    keep left right rectangles) := by
  subst D
  let D := actualCenteredHalfY1FineCoarseRectangleData base hbase fine
    physical fineLabels pointAt f f1 f2 outerA outerB hOuter hf hf1
    globalScale globalCenter ceiling exponent threshold fineT coarseDelta
    coarseT
  change D.goodPairs.Nonempty at hgood
  have hfamilies :=
    actualCenteredHalfY1_globalNormFamilies_nonempty_of_goodPairs
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT hgood
  let N := actualGlobalNormIndexData fine physical globalScale globalCenter
    exponent hfamilies.1 hradius hradiusSixteen hexponent
  have hfamily : N.family =
      actualGlobalNormIndexFamily fine physical globalScale globalCenter := rfl
  have hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j) := by
    intro i j
    rfl
  have hsymm : forall i j, N.distance i j = N.distance j i := by
    intro i j
    exact actualGlobalNormIndexData_distance_comm fine physical globalScale
      globalCenter exponent hfamilies.1 hradius hradiusSixteen hexponent i j
  have htriangle : forall i center j,
      N.distance i j <= N.distance i center + N.distance center j := by
    intro i center j
    exact projectedTubePairCoefficientDistance_triangle
      (fine.tubes i) (fine.tubes center) (fine.tubes j)
  have hballNonneg : 0 <= ballRadius :=
    (show (0 : Real) <= (radius : Real) from by positivity).trans hradiusBall
  have hnearRadiusLower : N.delta <= 10 * ballRadius := by
    change (radius : Real) <= 10 * ballRadius
    nlinarith
  have hballUpper : ballRadius <= N.ceiling := by
    change ballRadius <= 16
    nlinarith
  obtain ⟨bucket, hbucket, hbasePos, hselection⟩ :=
    exists_coarseDegreeBucket_with_retained_mass D hgood
  have hfiberSubset : forall R,
      R ∈ richCoarseRectangleFamily D
        (coarseDegreeBucketKeep D bucket)
        (automaticCanonicalRichness N ballRadius) ->
      D.coarseCurveIndexFiber (coarseDegreeBucketKeep D bucket) R ⊆
        N.family := by
    intro R _hR
    change D.coarseCurveIndexFiber (coarseDegreeBucketKeep D bucket) R ⊆
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    simpa only [D] using
      (actualCenteredHalfY1_coarseCurveIndexFiber_subset_globalNormIndexFamily
        base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
        hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
        coarseDelta coarseT (coarseDegreeBucketKeep D bucket) R)
  have hproduced := automaticPred_bucket_separatedPairLower_le_total
    N D ballRadius bucket hselection hfiberSubset hsymm hnearRadiusLower
      hnearRadiusUpper
  refine ⟨N, hfamily, hdistance, bucket, hbucket, hbasePos, hselection, ?_⟩
  intro hmassBlock
  let keep := coarseDegreeBucketKeep D bucket
  let lowerBound :=
    canonicalCoarseSeparatedPairProducedLower
      (automaticCanonicalRichness N ballRadius)
      (automaticCanonicalNearCap N ballRadius)
      (automaticRichRetainedMassLower D
        (automaticCanonicalNearCap N ballRadius)
        (2 * comparableBase bucket))
      (2 * comparableBase bucket)
  have hlowerPos : 0 < lowerBound := by
    exact automaticPred_bucket_separatedPairLower_pos N D ballRadius bucket
      hbasePos hmassBlock
  obtain ⟨left, hleft, right, hright, hseparated, hcoarseGood,
      _hcrossPositive, _hrichLower, _hwitness, hcrossSeparated,
      _hleftUpper, _hrightUpper⟩ :=
    exists_canonical_coarse_richSeparated_ballPair N D keep hsymm htriangle
      hradiusBall hballUpper hlowerPos hproduced
  let rectangles := actualGPrimeCommonCoarseRectangles D keep left right
  have hbridge := actualGPrimeCommonCoarseSamplingBridge fine physical
    globalScale globalCenter N D keep left right ballRadius hfamily hdistance
      hleft hright hcoarseGood hballNonneg hcrossSeparated
  refine ⟨keep, left, right, rectangles, ?_⟩
  exact {
    mass_block := hmassBlock
    keep_eq := rfl
    left_mem := hleft
    right_mem := hright
    canonical_separated := hseparated
    coarse_good := hcoarseGood
    cross_separated := hcrossSeparated
    rectangles_eq := rfl
    bridge := hbridge }

/-- A sharp concrete selection augmented by the actual finite random sample. -/
structure ActualConcreteGPrimeCommonCoarseSharpSampledOutcome
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
  selection : ActualConcreteGPrimeCommonCoarseSharpSamplingOutcome fine
    physical globalScale globalCenter N D ballRadius bucket keep left right
      rectangles
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

/-- Feed a sharp selected common fibre to the unchanged finite sampler. -/
theorem exists_actualConcreteGPrimeCommonCoarseSharpSample_of_bridge
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
    (O : ActualConcreteGPrimeCommonCoarseSharpSamplingOutcome fine physical
      globalScale globalCenter N D ballRadius bucket keep left right
        rectangles) :
    exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
      ActualConcreteGPrimeCommonCoarseSharpSampledOutcome fine physical
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

/-- End-to-end sharp E2 endpoint.  The displayed implication has exactly
the repaired dominance condition, with no spurious successor loss. -/
theorem exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSharpSample_of_E2Dominance
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
    (label : Int)
    (hcell : forall r, r ∈ D.fineLabels ->
      D.pointAt r ∈ projectedPositiveMultiplicityDyadicCell D.shading label)
    (hactive : forall r, r ∈ D.fineLabels ->
      (D.shading.activeAtPoint (D.pointAt r)).Nonempty)
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
        (coarseDegreeBucketLoss D *
            (automaticCanonicalRichness N ballRadius *
              (2 * comparableBase bucket)) <= pyzE2DegreeLower label ->
          exists keep : iota -> fineLabel -> Prop,
            exists left right : iota,
              exists rectangles : Finset C2GraphRectangle,
                exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
                  ActualConcreteGPrimeCommonCoarseSharpSampledOutcome fine
                    physical globalScale globalCenter N D ballRadius bucket
                      keep left right rectangles omega) := by
  obtain ⟨N, hfamily, hdistance, bucket, hbucket, hbasePos, hselection,
      hselectedIf⟩ :=
    exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSharpSamplingBridge
      base hbase fine physical fineLabels pointAt f f1 f2 outerA outerB
      hOuter hf hf1 globalScale globalCenter ceiling exponent threshold fineT
      coarseDelta coarseT D hD hgood hradius hradiusSixteen hexponent
      ballRadius hradiusBall hnearRadiusUpper
  refine ⟨N, hfamily, hdistance, bucket, hbucket, hbasePos, hselection, ?_⟩
  intro hdominance
  have hmassBlock := automaticPred_massBlock_of_E2Dominance N D ballRadius
    bucket label hgood hcell hactive hdominance
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
    exists_actualConcreteGPrimeCommonCoarseSharpSample_of_bridge fine physical
      globalScale globalCenter N D ballRadius bucket keep left right rectangles
      hfamily hfiberSubset O
  exact ⟨keep, left, right, rectangles, omega, hsample⟩

#print axioms ActualConcreteGPrimeCommonCoarseSharpSamplingOutcome
#print axioms exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSharpSamplingBridge
#print axioms ActualConcreteGPrimeCommonCoarseSharpSampledOutcome
#print axioms exists_actualConcreteGPrimeCommonCoarseSharpSample_of_bridge
#print axioms exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSharpSample_of_E2Dominance

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSharpBudgetSampleConnectorV1
