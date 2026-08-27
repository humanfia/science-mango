import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32ActualTubeCoefficientMetricV1
open FamilyStickyCinematicL32FiniteMetricMaximalCoverV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormSamplingLensAssemblyV1
open FamilyStickyCinematicL32Prop41ActualY1FixedCommonCSelectionConnectorV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
open FamilyStickyCinematicL32Prop41SeparatedCoefficientBallPairV1
open FamilyStickyCinematicL32TubePairTraceV1

noncomputable section

universe u v

local instance c2GraphRectangleDecidableEq : DecidableEq C2GraphRectangle :=
  Classical.decEq _

/-!
# G-prime common-fibre sampling bridge

A canonical G-prime pair is incident to the literal common coarse-rectangle
fibre.  Its two centres therefore give one point in every corresponding
closed metric ball.  At sampling moduli `mu = nu = 1`, this is exactly the
richness input used by the shared-global sampler.

The cross-separation field below is also transported to every pair of
genuine survivor hits.  Fixing `pairScale = 4 * ballRadius` makes the
canonical `8 * ballRadius` separation definitionally the coefficient lower
bound required by the paper-fine uniform producer.
-/

/-- The full literal common coarse-rectangle fibre of a selected G-prime
pair. -/
noncomputable def actualGPrimeCommonCoarseRectangles
    {point : Type*} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota) :
    Finset C2GraphRectangle :=
  D.commonCoarseRectangleFiber keep left right

@[simp]
theorem actualGPrimeCommonCoarseRectangles_card
    {point : Type*} [MeasurableSpace point]
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (D : CoarseRectangleIncidenceData
      (point := point) (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota) :
    (actualGPrimeCommonCoarseRectangles D keep left right).card =
      D.coarseCrossIncidenceCount keep left right := by
  rfl

/-- The mechanically generated sampling data attached to one canonical
G-prime pair.  No common-fine-label, fixed-`c`, or reference assertion is
included. -/
structure ActualGPrimeCommonCoarseSamplingBridge
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) : Prop where
  rectangles_nonempty :
    (actualGPrimeCommonCoarseRectangles D keep left right).Nonempty
  rectangles_card_eq_cross_count :
    (actualGPrimeCommonCoarseRectangles D keep left right).card =
      D.coarseCrossIncidenceCount keep left right
  cross_count_pos : 0 < D.coarseCrossIncidenceCount keep left right
  left_rich_one : forall R :
      actualGPrimeCommonCoarseRectangles D keep left right,
    1 <= (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep (actualGPrimeCommonCoarseRectangles D keep left right)
        ballRadius (D.fine.tubes left) R).card
  right_rich_one : forall R :
      actualGPrimeCommonCoarseRectangles D keep left right,
    1 <= (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
      globalCenter D keep (actualGPrimeCommonCoarseRectangles D keep left right)
        ballRadius (D.fine.tubes right) R).card
  survivor_pair_separated : forall omega :
      (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin 1) ×
        (actualGlobalNormIndexFamily fine physical globalScale globalCenter ->
          Fin 1),
    forall S : ActualSharedGlobalSurvivorItem fine physical globalScale
      globalCenter D keep
        (actualGPrimeCommonCoarseRectangles D keep left right)
        (D.fine.tubes left) (D.fine.tubes right) ballRadius 1 1 omega,
      2 * (4 * ballRadius) <= tubePairCoefficientDistance
        (D.fine.tubes (actualSharedGlobalSurvivorLeftIndex fine physical
          globalScale globalCenter D keep
            (actualGPrimeCommonCoarseRectangles D keep left right)
            (D.fine.tubes left) (D.fine.tubes right) ballRadius 1 1 omega S))
        (D.fine.tubes (actualSharedGlobalSurvivorRightIndex fine physical
          globalScale globalCenter D keep
            (actualGPrimeCommonCoarseRectangles D keep left right)
            (D.fine.tubes left) (D.fine.tubes right) ballRadius 1 1 omega S))

/-- Projected and paper-fine reduced coefficient distances are the same
literal `(a,b,d)` distance. -/
theorem tubePairCoefficientDistance_eq_projectedTubePairCoefficientDistance
    {radius : NNReal} (T U : Tube radius) :
    tubePairCoefficientDistance T U =
      projectedTubePairCoefficientDistance T U := by
  rfl

/-- Produce the complete `mu = nu = 1` sampling bridge from a canonical
G-prime pair and the cross-separation of its two metric balls. -/
theorem actualGPrimeCommonCoarseSamplingBridge
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (fine : UniformTubeFamily radius iota)
    (physical : FiniteProjectedShading (Real × Real) iota)
    (globalScale : Real) (globalCenter : Tube radius)
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical globalScale globalCenter)
    (hdistance : forall i j, N.distance i j =
      projectedTubePairCoefficientDistance
        (D.fine.tubes i) (D.fine.tubes j))
    (hleft : left ∈ N.family) (hright : right ∈ N.family)
    (hcoarseGood : D.CoarseGoodPair keep left right)
    (hballRadius : 0 <= ballRadius)
    (hcross : FiniteFamiliesCrossSeparated N.distance (8 * ballRadius)
      (finiteFamilyMetricBall N.family N.distance ballRadius left)
      (finiteFamilyMetricBall N.family N.distance ballRadius right)) :
    ActualGPrimeCommonCoarseSamplingBridge fine physical globalScale
      globalCenter D keep left right ballRadius := by
  let rectangles := actualGPrimeCommonCoarseRectangles D keep left right
  let ambient :=
    actualGlobalNormIndexFamily fine physical globalScale globalCenter
  have hleftAmbient : left ∈ ambient := by
    change left ∈
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    rw [← hfamily]
    exact hleft
  have hrightAmbient : right ∈ ambient := by
    change right ∈
      actualGlobalNormIndexFamily fine physical globalScale globalCenter
    rw [← hfamily]
    exact hright
  refine {
    rectangles_nonempty := ?_
    rectangles_card_eq_cross_count := ?_
    cross_count_pos := ?_
    left_rich_one := ?_
    right_rich_one := ?_
    survivor_pair_separated := ?_ }
  · simpa only [rectangles, actualGPrimeCommonCoarseRectangles,
      CoarseRectangleIncidenceData.CoarseGoodPair] using hcoarseGood
  · exact actualGPrimeCommonCoarseRectangles_card D keep left right
  · exact (D.coarseGoodPair_iff_crossIncidence_pos keep left right).mp
      hcoarseGood
  · intro R
    apply Finset.one_le_card.mpr
    let leftInAmbient : ambient := ⟨left, hleftAmbient⟩
    refine ⟨leftInAmbient, ?_⟩
    apply (mem_ambientSubtypeRestriction_iff ambient
      (D.coarseCurveMetricBall keep R.1
        projectedTubePairCoefficientDistance ballRadius
          (D.fine.tubes left)) leftInAmbient).mpr
    apply (D.mem_coarseCurveMetricBall_iff keep).mpr
    constructor
    · exact ((D.mem_commonCoarseRectangleFiber_iff keep).mp R.2).2.1
    · rw [projectedTubePairCoefficientDistance_self]
      exact hballRadius
  · intro R
    apply Finset.one_le_card.mpr
    let rightInAmbient : ambient := ⟨right, hrightAmbient⟩
    refine ⟨rightInAmbient, ?_⟩
    apply (mem_ambientSubtypeRestriction_iff ambient
      (D.coarseCurveMetricBall keep R.1
        projectedTubePairCoefficientDistance ballRadius
          (D.fine.tubes right)) rightInAmbient).mpr
    apply (D.mem_coarseCurveMetricBall_iff keep).mpr
    constructor
    · exact ((D.mem_commonCoarseRectangleFiber_iff keep).mp R.2).2.2
    · rw [projectedTubePairCoefficientDistance_self]
      exact hballRadius
  · intro omega S
    let leftIndex := actualSharedGlobalSurvivorLeftIndex fine physical
      globalScale globalCenter D keep rectangles (D.fine.tubes left)
        (D.fine.tubes right) ballRadius 1 1 omega S
    let rightIndex := actualSharedGlobalSurvivorRightIndex fine physical
      globalScale globalCenter D keep rectangles (D.fine.tubes left)
        (D.fine.tubes right) ballRadius 1 1 omega S
    have hleftMetric :=
      actualSharedGlobal_survivorLeftHit_mem_coarseCurveMetricBall
        fine physical globalScale globalCenter D keep rectangles
          (D.fine.tubes left) (D.fine.tubes right) ballRadius 1 1 omega S
    have hrightMetric :=
      actualSharedGlobal_survivorRightHit_mem_coarseCurveMetricBall
        fine physical globalScale globalCenter D keep rectangles
          (D.fine.tubes left) (D.fine.tubes right) ballRadius 1 1 omega S
    have hleftN : leftIndex ∈ N.family := by
      rw [hfamily]
      exact (survivorLeftHitWitness 1 1
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius (D.fine.tubes left))
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius (D.fine.tubes right))
        omega S).1.2
    have hrightN : rightIndex ∈ N.family := by
      rw [hfamily]
      exact (survivorRightHitWitness 1 1
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius (D.fine.tubes left))
        (actualSharedGlobalCoarseCurveNeighbors fine physical globalScale
          globalCenter D keep rectangles ballRadius (D.fine.tubes right))
        omega S).1.2
    have hleftBall : leftIndex ∈
        finiteFamilyMetricBall N.family N.distance ballRadius left := by
      apply Finset.mem_filter.mpr
      refine ⟨hleftN, ?_⟩
      rw [hdistance]
      exact ((D.mem_coarseCurveMetricBall_iff keep).mp hleftMetric).2
    have hrightBall : rightIndex ∈
        finiteFamilyMetricBall N.family N.distance ballRadius right := by
      apply Finset.mem_filter.mpr
      refine ⟨hrightN, ?_⟩
      rw [hdistance]
      exact ((D.mem_coarseCurveMetricBall_iff keep).mp hrightMetric).2
    have hseparated : 8 * ballRadius <=
        projectedTubePairCoefficientDistance
          (D.fine.tubes leftIndex) (D.fine.tubes rightIndex) := by
      rw [← hdistance]
      exact hcross leftIndex hleftBall rightIndex hrightBall
    calc
      2 * (4 * ballRadius) = 8 * ballRadius := by ring
      _ <= projectedTubePairCoefficientDistance
          (D.fine.tubes leftIndex) (D.fine.tubes rightIndex) := hseparated
      _ = tubePairCoefficientDistance
          (D.fine.tubes leftIndex) (D.fine.tubes rightIndex) :=
        (tubePairCoefficientDistance_eq_projectedTubePairCoefficientDistance
          (D.fine.tubes leftIndex) (D.fine.tubes rightIndex)).symm

#print axioms actualGPrimeCommonCoarseRectangles_card
#print axioms tubePairCoefficientDistance_eq_projectedTubePairCoefficientDistance
#print axioms ActualGPrimeCommonCoarseSamplingBridge
#print axioms actualGPrimeCommonCoarseSamplingBridge

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeSamplingBridgeV1
