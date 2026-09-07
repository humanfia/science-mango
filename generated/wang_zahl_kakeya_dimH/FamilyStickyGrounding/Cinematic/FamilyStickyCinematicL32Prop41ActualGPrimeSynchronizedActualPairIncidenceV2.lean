import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedLabelMultiplicityV3
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairIncidenceV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41ActualGPrimeArbitrarySeparatedPairWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41ActualGPrimeGlobalGridShiftSynchronizationV6
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedLabelMultiplicityV3
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridWeightedUniformPackageV2
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CanonicalRichSeparatedPairConsumerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRichSeparatedPairSelectionV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

/-!
# Actual endpoint-pair incidence behind synchronized package multiplicity

The exact label multiplicity from the preceding module counts dependent
survivors, not centre pairs.  Here those occurrences are kept as an honest
dependent finite sum and mapped to their literal pair of fine indices.

A centre pair is separated by `10 * R`, while a sampled endpoint may move by
`R` on either side.  Thus the endpoint pair is certified at separation
`8 * R`, equivalently at the canonical separation radius `4 * R / 5`.
No claim at the original radius `R` is made.
-/

/-- Radius at which a survivor endpoint pair remains canonically separated. -/
def actualGPrimeSurvivorSeparationRadius (ballRadius : Real) : Real :=
  4 * ballRadius / 5

/-- Dependent type of all survivor occurrences over a centre-pair carrier. -/
abbrev ActualGPrimeSynchronizedOccurrence
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (activePairs : Finset (iota × iota))
    (packageAt : forall pair : {p // p ∈ activePairs},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal) :=
  Sigma fun pair : {p // p ∈ activePairs} =>
    ActualGPrimeLabelFirstSurvivor N D keep pair.1.1 pair.1.2 ballRadius
      (packageAt pair).omega

/-- Literal occurrence carrier for one fine label. -/
noncomputable def actualGPrimeSynchronizedLabelOccurrences
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (activePairs : Finset (iota × iota))
    (packageAt : forall pair : {p // p ∈ activePairs},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (selectedPairs : Finset {p // p ∈ activePairs}) (r : fineLabel) :
    Finset (ActualGPrimeSynchronizedOccurrence fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal activePairs packageAt) :=
  selectedPairs.sigma fun pair =>
    (packageAt pair).package.selected.filter fun a =>
      actualGPrimeLabelFirstLabel N D keep pair.1.1 pair.1.2 ballRadius
        (packageAt pair).omega a = r

/-- Literal pair of original fine indices represented by an occurrence. -/
noncomputable def actualGPrimeSynchronizedOccurrenceFinePair
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (activePairs : Finset (iota × iota))
    (packageAt : forall pair : {p // p ∈ activePairs},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (x : ActualGPrimeSynchronizedOccurrence fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal activePairs packageAt) :
    iota × iota :=
  (actualGPrimeLabelFirstLeftIndex N D keep x.1.1.1 x.1.1.2 ballRadius
      (packageAt x.1).omega x.2,
    actualGPrimeLabelFirstRightIndex N D keep x.1.1.1 x.1.1.2 ballRadius
      (packageAt x.1).omega x.2)

/-- The occurrence carrier has exactly the previously defined label
multiplicity. -/
theorem actualGPrimeSynchronizedLabelOccurrences_card
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (activePairs : Finset (iota × iota))
    (packageAt : forall pair : {p // p ∈ activePairs},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (selectedPairs : Finset {p // p ∈ activePairs}) (r : fineLabel) :
    (actualGPrimeSynchronizedLabelOccurrences fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal activePairs packageAt
        selectedPairs r).card =
      actualGPrimeSynchronizedLabelMultiplicity fine N D keep ballRadius
        labelWeight f outerA outerB globalDelta tGlobal activePairs packageAt
          selectedPairs r := by
  classical
  simp only [actualGPrimeSynchronizedLabelOccurrences, Finset.card_sigma,
    actualGPrimeSynchronizedLabelMultiplicity]

/-- The sampled left endpoint lies in the radius-`R` metric ball about its
centre. -/
theorem actualGPrimeLabelFirstLeftIndex_distance_center_le
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :
    N.distance
        (actualGPrimeLabelFirstLeftIndex
          N D keep left right ballRadius omega a) left <= ballRadius := by
  let labels := actualGPrimeBilateralRetainedFineLabels
    N D keep left right ballRadius
  let leftNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r.1
  let rightNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r.1
  have hmem := (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors
    omega a).2.1
  exact (mem_actualGPrimeRetainedFineMetricNeighbors_iff
    N D keep left ballRadius a.1.1
      (survivorLeftHitWitness 1 1 leftNeighbors rightNeighbors omega a).1).mp
        hmem |>.2

/-- The sampled right endpoint lies in the radius-`R` metric ball about its
centre. -/
theorem actualGPrimeLabelFirstRightIndex_distance_center_le
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (a : ActualGPrimeLabelFirstSurvivor
      N D keep left right ballRadius omega) :
    N.distance
        (actualGPrimeLabelFirstRightIndex
          N D keep left right ballRadius omega a) right <= ballRadius := by
  let labels := actualGPrimeBilateralRetainedFineLabels
    N D keep left right ballRadius
  let leftNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r.1
  let rightNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r.1
  have hmem := (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors
    omega a).2.1
  exact (mem_actualGPrimeRetainedFineMetricNeighbors_iff
    N D keep right ballRadius a.1.1
      (survivorRightHitWitness 1 1 leftNeighbors rightNeighbors omega a).1).mp
        hmem |>.2

/-- Every selected occurrence maps to a literal retained fine-index pair at
the sharp surviving separation radius `4R/5`. -/
theorem actualGPrimeSynchronizedOccurrenceFinePair_mem
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (ballRadius : Real)
    (labelWeight : fineLabel -> ENNReal)
    (f : Real -> Real) (outerA outerB globalDelta tGlobal : Real)
    (activePairs : Finset (iota × iota))
    (packageAt : forall pair : {p // p ∈ activePairs},
      ActualGPrimeArbitrarySeparatedPairWeightedUniformOutcome
        fine N D keep pair.1 ballRadius labelWeight f outerA outerB
          globalDelta tGlobal)
    (selectedPairs : Finset {p // p ∈ activePairs}) (r : fineLabel)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (x : ActualGPrimeSynchronizedOccurrence fine N D keep ballRadius
      labelWeight f outerA outerB globalDelta tGlobal activePairs packageAt)
    (hx : x ∈ actualGPrimeSynchronizedLabelOccurrences fine N D keep
      ballRadius labelWeight f outerA outerB globalDelta tGlobal activePairs
        packageAt selectedPairs r) :
    actualGPrimeSynchronizedOccurrenceFinePair fine N D keep ballRadius
        labelWeight f outerA outerB globalDelta tGlobal activePairs packageAt x
      ∈ actualGPrimeFineSeparatedPairsAt N D keep
        (actualGPrimeSurvivorSeparationRadius ballRadius) r := by
  classical
  rcases x with ⟨pair, a⟩
  have hxData := Finset.mem_sigma.mp hx
  have haData := Finset.mem_filter.mp hxData.2
  have hleftFamily := actualGPrimeLabelFirstLeftIndex_mem_family
    N D keep pair.1.1 pair.1.2 ballRadius (packageAt pair).omega a
  have hrightFamily := actualGPrimeLabelFirstRightIndex_mem_family
    N D keep pair.1.1 pair.1.2 ballRadius (packageAt pair).omega a
  have hleftActive :
      actualGPrimeLabelFirstLeftIndex N D keep pair.1.1 pair.1.2 ballRadius
          (packageAt pair).omega a ∈
        actualGPrimeRetainedFineActiveFiber N D keep r := by
    apply (mem_actualGPrimeRetainedFineActiveFiber_iff N D keep r _).mpr
    exact ⟨by simpa only [haData.2] using
      (packageAt pair).package.left_retained a haData.1, hleftFamily⟩
  have hrightActive :
      actualGPrimeLabelFirstRightIndex N D keep pair.1.1 pair.1.2 ballRadius
          (packageAt pair).omega a ∈
        actualGPrimeRetainedFineActiveFiber N D keep r := by
    apply (mem_actualGPrimeRetainedFineActiveFiber_iff N D keep r _).mpr
    exact ⟨by simpa only [haData.2] using
      (packageAt pair).package.right_retained a haData.1, hrightFamily⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hleftActive, hrightActive⟩, ?_⟩
  unfold canonicalTenRadiusSeparated actualGPrimeSurvivorSeparationRadius
  have hcoefficient :=
    (packageAt pair).package.gridSelection.coefficient_lower a
      ((packageAt pair).package.selected_subset_grid haData.1)
  calc
    10 * (4 * ballRadius / 5) = 2 * (4 * ballRadius) := by ring
    _ <= tubePairCoefficientDistance
        (D.fine.tubes (actualGPrimeLabelFirstLeftIndex N D keep pair.1.1
          pair.1.2 ballRadius (packageAt pair).omega a))
        (D.fine.tubes (actualGPrimeLabelFirstRightIndex N D keep pair.1.1
          pair.1.2 ballRadius (packageAt pair).omega a)) := by
      simpa only [tubePairCoefficientDistance_threeShiftCGridNormalizeTube]
        using hcoefficient
    _ = projectedTubePairCoefficientDistance
        (D.fine.tubes (actualGPrimeLabelFirstLeftIndex N D keep pair.1.1
          pair.1.2 ballRadius (packageAt pair).omega a))
        (D.fine.tubes (actualGPrimeLabelFirstRightIndex N D keep pair.1.1
          pair.1.2 ballRadius (packageAt pair).omega a)) :=
      tubePairCoefficientDistance_eq_projectedTubePairCoefficientDistance _ _
    _ = N.distance
        (actualGPrimeLabelFirstLeftIndex N D keep pair.1.1 pair.1.2 ballRadius
          (packageAt pair).omega a)
        (actualGPrimeLabelFirstRightIndex N D keep pair.1.1 pair.1.2 ballRadius
          (packageAt pair).omega a) := (hdistance _ _).symm

#print axioms actualGPrimeSurvivorSeparationRadius
#print axioms actualGPrimeSynchronizedLabelOccurrences_card
#print axioms actualGPrimeLabelFirstLeftIndex_distance_center_le
#print axioms actualGPrimeLabelFirstRightIndex_distance_center_le
#print axioms actualGPrimeSynchronizedOccurrenceFinePair_mem

end

end FamilyStickyCinematicL32Prop41ActualGPrimeSynchronizedActualPairIncidenceV2
