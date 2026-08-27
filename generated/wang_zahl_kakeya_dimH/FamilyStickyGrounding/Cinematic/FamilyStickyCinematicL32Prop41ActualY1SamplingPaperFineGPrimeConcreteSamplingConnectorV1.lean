import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeConcreteSamplingConnectorV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring.ComparableMultiplicityBuckets
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalCoarseSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CanonicalSeparatedBallPairV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1

noncomputable section

universe u v

/-!
# Concrete G-prime to common-fibre sampling connector

This module keeps the canonical norm datum concrete until its distance and
family fields have been connected to the actual incidence datum.  Once the
selected degree bucket contains one full mass block, it returns the selected
centres, the bucket keep predicate, the literal common coarse-rectangle
fibre, and the complete `mu = nu = 1` bridge.
-/

/-- The selected concrete output after positivity of the chosen G-prime mass
block. -/
structure ActualConcreteGPrimeCommonCoarseSamplingOutcome
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
        (automaticCanonicalRichness N ballRadius)
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

/-- The actual centered-half-Y1 G-prime producer, kept at its concrete
`actualGlobalNormIndexData`, feeds the full common-fibre sampling bridge.
The conclusion exposes both compatibility equations.  The final implication
is the sole mass-block positivity input already isolated by the G-prime
producer. -/
theorem exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSamplingBridge
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
              (automaticCanonicalRichness N ballRadius)
              (2 * comparableBase bucket) ->
          exists keep : iota -> fineLabel -> Prop,
            exists left right : iota,
              exists rectangles : Finset C2GraphRectangle,
                ActualConcreteGPrimeCommonCoarseSamplingOutcome fine physical
                  globalScale globalCenter N D ballRadius bucket keep left right
                    rectangles) := by
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
      actualGlobalNormIndexFamily fine physical globalScale globalCenter := by
    rfl
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
  obtain ⟨bucket, hbucket, hbasePos, hselection, hproducedIf⟩ :=
    exists_actualGPrime_bucket_separatedPairLower N D ballRadius hgood hsymm
      hnearRadiusLower hnearRadiusUpper
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
  have hproduced := hproducedIf hfiberSubset
  refine ⟨N, hfamily, hdistance, bucket, hbucket, hbasePos, hselection, ?_⟩
  intro hmassBlock
  let keep := coarseDegreeBucketKeep D bucket
  let lowerBound :=
    canonicalCoarseSeparatedPairProducedLower
      (automaticCanonicalRichness N ballRadius)
      (automaticCanonicalNearCap N ballRadius)
      (automaticRichRetainedMassLower D
        (automaticCanonicalRichness N ballRadius)
        (2 * comparableBase bucket))
      (2 * comparableBase bucket)
  have hlowerPos : 0 < lowerBound := by
    exact automatic_bucket_separatedPairLower_pos N D ballRadius bucket
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

#print axioms ActualConcreteGPrimeCommonCoarseSamplingOutcome
#print axioms exists_actualCenteredHalfY1_globalNorm_GPrime_commonCoarseSamplingBridge

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeConcreteSamplingConnectorV1
