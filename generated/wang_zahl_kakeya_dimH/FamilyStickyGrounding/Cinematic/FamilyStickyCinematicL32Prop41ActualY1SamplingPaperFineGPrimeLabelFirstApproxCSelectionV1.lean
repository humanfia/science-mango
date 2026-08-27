import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyWZ2TubeCarrierCoordinateAdapterV1
open FamilyStickyCinematicL32ActualProjectedCenteredHalfY1ActiveGeometryV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualY1FineCoarseRectangleProducerV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v w

/-!
# Approximate-C label-first pair selection

The ordinary label-first sampler already supplies two retained incidences at
the same fine label.  In the literal `Y1` data, both active tubes lie in the
same radius/2 graph-C bucket around the source tube.  Hence their graph-C
coordinates differ by at most one tube radius.  This is the honest input for
the later C-normalization step; no exact-C fibre or fixed global-C provenance
is assumed.
-/

/-- Retained same-label pairs with a quantitative graph-C gap. -/
structure ActualRetainedY1ApproxCPairSelection
    {point : Type u} [MeasurableSpace point]
    {radius : NNReal} {iota : Type v} [DecidableEq iota]
    {fineLabel : Type w} [DecidableEq fineLabel]
    {alpha : Type*}
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (items : Finset alpha)
    (leftIndex rightIndex : alpha -> iota)
    (labelAt : alpha -> fineLabel)
    (keep : iota -> fineLabel -> Prop)
    (pairScale cError : Real) : Prop where
  left_retained : forall a, a ∈ items ->
    (leftIndex a, labelAt a) ∈ D.retainedGoodPairs keep
  right_retained : forall a, a ∈ items ->
    (rightIndex a, labelAt a) ∈ D.retainedGoodPairs keep
  c_gap : forall a, a ∈ items ->
    |tubeGraphC (D.fine.tubes (leftIndex a)) -
      tubeGraphC (D.fine.tubes (rightIndex a))| <= cError
  coefficient_lower : forall a, a ∈ items ->
    2 * pairScale <= tubePairCoefficientDistance
      (D.fine.tubes (leftIndex a)) (D.fine.tubes (rightIndex a))

/-- Two retained incidences at one literal `Y1` fine label have graph-C gap
at most the tube radius. -/
theorem retainedY1_sameLabel_cGap_le_radius
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (fineDelta fineScale coarseDelta coarseScale : Real)
    (keep : iota -> fineLabel -> Prop)
    (leftIndex rightIndex : iota) (r : fineLabel)
    (hleft : (leftIndex, r) ∈
      ((y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 fineDelta fineScale coarseDelta
          coarseScale).retainedGoodPairs keep))
    (hright : (rightIndex, r) ∈
      ((y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
        f f1 f2 hf hf1 fineDelta fineScale coarseDelta
          coarseScale).retainedGoodPairs keep)) :
    |tubeGraphC (fine.tubes leftIndex) -
      tubeGraphC (fine.tubes rightIndex)| <= (radius : Real) := by
  have hleftActive := y1FineCoarseRectangleData_retainedPair_active
    fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1 fineDelta fineScale
      coarseDelta coarseScale keep leftIndex r hleft
  have hrightActive := y1FineCoarseRectangleData_retainedPair_active
    fine Y1 fineLabels pointAt tubeAt f f1 f2 hf hf1 fineDelta fineScale
      coarseDelta coarseScale keep rightIndex r hright
  have hqE : pointAt r ∈ E := hpointE r hleftActive.1
  have hleftC := facts.hactiveCBucket
    (pointAt r) hqE leftIndex hleftActive.2.1
  have hrightC := facts.hactiveCBucket
    (pointAt r) hqE rightIndex hrightActive.2.1
  have htriangle :
      |tubeGraphC (fine.tubes leftIndex) -
          tubeGraphC (fine.tubes rightIndex)| <=
        |tubeGraphC (fine.tubes leftIndex) - tubeGraphC (tubeAt (pointAt r))| +
          |tubeGraphC (tubeAt (pointAt r)) -
            tubeGraphC (fine.tubes rightIndex)| := by
    calc
      |tubeGraphC (fine.tubes leftIndex) -
          tubeGraphC (fine.tubes rightIndex)| =
        |(tubeGraphC (fine.tubes leftIndex) - tubeGraphC (tubeAt (pointAt r))) +
          (tubeGraphC (tubeAt (pointAt r)) -
            tubeGraphC (fine.tubes rightIndex))| := by ring_nf
      _ <= _ := abs_add_le _ _
  calc
    |tubeGraphC (fine.tubes leftIndex) -
        tubeGraphC (fine.tubes rightIndex)| <=
      |tubeGraphC (fine.tubes leftIndex) - tubeGraphC (tubeAt (pointAt r))| +
        |tubeGraphC (tubeAt (pointAt r)) -
          tubeGraphC (fine.tubes rightIndex)| := htriangle
    _ <= (radius : Real) / 2 + (radius : Real) / 2 := by
      gcongr
      simpa only [abs_sub_comm] using hrightC
    _ = (radius : Real) := by ring

/-- Ordinary label-first G-prime survivors form an approximate-C retained
pair selection, with no fixed-C provenance input. -/
theorem actualGPrimeLabelFirst_actualRetainedY1ApproxCPairSelection
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (E : Set (Real × Real))
    (Y1 : FiniteProjectedShading (Real × Real) iota)
    (fineLabels : Finset fineLabel) (pointAt : fineLabel -> Real × Real)
    (tubeAt : Real × Real -> Tube radius)
    (f f1 f2 : Real -> Real) (outerA outerB : Real)
    (hOuter : outerA <= outerB)
    (hf : forall z, HasDerivAt f (f1 z) z)
    (hf1 : forall z, HasDerivAt f1 (f2 z) z)
    (tGlobal globalDelta : Real)
    (facts : ActualCenteredHalfY1ActiveGeometryFacts fine physical E
      Y1.activeAtPoint tubeAt f f1 f2 outerA outerB hOuter hf hf1
      tGlobal globalDelta)
    (hpointE : forall r, r ∈ fineLabels -> pointAt r ∈ E)
    (fineDelta fineScale coarseDelta coarseScale : Real)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (hD : D = y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
      f f1 f2 hf hf1 fineDelta fineScale coarseDelta coarseScale)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (hcross : FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
      (finiteFamilyMetricBall N.family N.distance ballRadius left)
      (finiteFamilyMetricBall N.family N.distance ballRadius right))
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    ActualRetainedY1ApproxCPairSelection D
      (Finset.univ : Finset (ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega))
      (actualGPrimeLabelFirstLeftIndex N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega)
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
      keep (4 * ballRadius) (radius : Real) := by
  classical
  subst D
  let D := y1FineCoarseRectangleData fine Y1 fineLabels pointAt tubeAt
    f f1 f2 hf hf1 fineDelta fineScale coarseDelta coarseScale
  let labels := actualGPrimeBilateralRetainedFineLabels
    N D keep left right ballRadius
  let leftNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r.1
  let rightNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r.1
  constructor
  · intro S _hS
    have hmem := (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors
      omega S).2.1
    exact (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep left ballRadius S.1.1
        (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
          hmem |>.1
  · intro S _hS
    have hmem := (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors
      omega S).2.1
    exact (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep right ballRadius S.1.1
        (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
          hmem |>.1
  · intro S _hS
    apply retainedY1_sameLabel_cGap_le_radius fine physical E Y1 fineLabels
      pointAt tubeAt f f1 f2 outerA outerB hOuter hf hf1 tGlobal globalDelta
      facts hpointE fineDelta fineScale coarseDelta coarseScale keep
      (actualGPrimeLabelFirstLeftIndex N D keep left right ballRadius omega S)
      (actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega S)
      (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega S)
    · exact (mem_actualGPrimeRetainedFineMetricNeighbors_iff
        N D keep left ballRadius S.1.1
          (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
            (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega S).2.1 |>.1
    · exact (mem_actualGPrimeRetainedFineMetricNeighbors_iff
        N D keep right ballRadius S.1.1
          (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega S).1).mp
            (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega S).2.1 |>.1
  · intro S _hS
    let leftHit := survivorLeftHitWitness 1 1
      leftNeighbors rightNeighbors omega S
    let rightHit := survivorRightHitWitness 1 1
      leftNeighbors rightNeighbors omega S
    have hleftData := (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep left ballRadius S.1.1 leftHit.1).mp leftHit.2.1
    have hrightData := (mem_actualGPrimeRetainedFineMetricNeighbors_iff
      N D keep right ballRadius S.1.1 rightHit.1).mp rightHit.2.1
    have hleftBall : leftHit.1.1 ∈
        finiteFamilyMetricBall N.family N.distance ballRadius left :=
      Finset.mem_filter.mpr ⟨leftHit.1.2, hleftData.2⟩
    have hrightBall : rightHit.1.1 ∈
        finiteFamilyMetricBall N.family N.distance ballRadius right :=
      Finset.mem_filter.mpr ⟨rightHit.1.2, hrightData.2⟩
    have hsep := hcross leftHit.1.1 hleftBall rightHit.1.1 hrightBall
    calc
      2 * (4 * ballRadius) = 8 * ballRadius := by ring
      _ <= N.distance leftHit.1.1 rightHit.1.1 := hsep
      _ = projectedTubePairCoefficientDistance
          (D.fine.tubes leftHit.1.1) (D.fine.tubes rightHit.1.1) :=
        hdistance _ _
      _ = tubePairCoefficientDistance
          (D.fine.tubes leftHit.1.1) (D.fine.tubes rightHit.1.1) :=
        (tubePairCoefficientDistance_eq_projectedTubePairCoefficientDistance
          (D.fine.tubes leftHit.1.1) (D.fine.tubes rightHit.1.1)).symm

#print axioms ActualRetainedY1ApproxCPairSelection
#print axioms retainedY1_sameLabel_cGap_le_radius
#print axioms actualGPrimeLabelFirst_actualRetainedY1ApproxCPairSelection

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstApproxCSelectionV1
