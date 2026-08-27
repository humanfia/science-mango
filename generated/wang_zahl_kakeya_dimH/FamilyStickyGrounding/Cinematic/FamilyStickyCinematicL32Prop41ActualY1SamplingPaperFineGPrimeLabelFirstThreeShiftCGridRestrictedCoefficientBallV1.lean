import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticReferenceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32TubePairTraceV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41ActualSharedGlobalSurvivorAutomaticReferenceV1
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionPairReindexV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineSelectedAutomaticReferenceV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridCanonicalFibresV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
open FamilyStickyCinematicL32ThreeShiftCGridTubeNormalizationV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

section Ball

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {fineLabel : Type v} [DecidableEq fineLabel]
variable (fine : UniformTubeFamily radius iota)
variable (physical : FiniteProjectedShading (Real × Real) iota)
variable (tGlobal : Real) (globalCenter : Tube radius)
variable (N : CanonicalNormNonconcentrationData iota)
variable (D : CoarseRectangleIncidenceData (point := Real × Real)
  (radius := radius) (iota := iota) fineLabel)
variable (keep : iota -> fineLabel -> Prop) (left right : iota)
variable (ballRadius : Real)
variable (omega : (N.family -> Fin 1) × (N.family -> Fin 1))

private abbrev Survivor := ActualGPrimeLabelFirstSurvivor
  N D keep left right ballRadius omega

private def leftNeighbors
    (r : actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius) : Finset N.family :=
  actualGPrimeRetainedFineMetricNeighbors N D keep left ballRadius r.1

private def rightNeighbors
    (r : actualGPrimeBilateralRetainedFineLabels
      N D keep left right ballRadius) : Finset N.family :=
  actualGPrimeRetainedFineMetricNeighbors N D keep right ballRadius r.1

theorem actualGPrimeLabelFirstLeftIndex_mem_family
    (a : Survivor N D keep left right ballRadius omega) :
    actualGPrimeLabelFirstLeftIndex
      N D keep left right ballRadius omega a ∈ N.family := by
  exact (survivorLeftHitWitness 1 1
    (leftNeighbors N D keep left right ballRadius)
    (rightNeighbors N D keep left right ballRadius) omega a).1.2

theorem actualGPrimeLabelFirstRightIndex_mem_family
    (a : Survivor N D keep left right ballRadius omega) :
    actualGPrimeLabelFirstRightIndex
      N D keep left right ballRadius omega a ∈ N.family := by
  exact (survivorRightHitWitness 1 1
    (leftNeighbors N D keep left right ballRadius)
    (rightNeighbors N D keep left right ballRadius) omega a).1.2

/-- Snapping C does not affect the reduced coefficient distance, so any
index in the actual global-norm family keeps its original `3 * tGlobal`
bound. -/
theorem threeShiftCGridNormalizeTube_distance_le_three_mul_of_mem_family
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (k : Fin 3) {i : iota} (hi : i ∈ N.family) :
    tubePairCoefficientDistance
        (threeShiftCGridNormalizeTube k (D.fine.tubes i)) globalCenter <=
      3 * tGlobal := by
  let j : actualGlobalNormIndexFamily fine physical tGlobal globalCenter :=
    ⟨i, by rw [← hfamily]; exact hi⟩
  have hbase := actualGlobalNormIndex_tube_distance_le_three_mul fine
    physical tGlobal globalCenter j
  change tubePairCoefficientDistance (fine.tubes i) globalCenter <=
    3 * tGlobal at hbase
  rw [hDfine]
  simpa only [threeShiftCGridNormalizeTube,
    tubePairCoefficientDistance_normalizeTubeC_left] using hbase

variable {items : Finset (Survivor N D keep left right ballRadius omega)}
variable {pairScale : Real}
variable (P : ActualRetainedY1ThreeShiftCGridSelection D items
  (actualGPrimeLabelFirstLeftIndex N D keep left right ballRadius omega)
  (actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega)
  (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
  keep pairScale)

/-- Exact bound for a final left endpoint: grid snapping is free in the
reduced metric and the fixed trace translation costs at most `|shift|`. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedTraceLeftTube_distance_le
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (shift : Real) (a : Survivor N D keep left right ballRadius omega) :
    tubePairCoefficientDistance
        (actualThreeShiftCGridRestrictedTraceLeftTube P shift a)
        globalCenter <= 3 * tGlobal + |shift| := by
  have hbase :=
    threeShiftCGridNormalizeTube_distance_le_three_mul_of_mem_family
      fine physical tGlobal globalCenter N D hDfine hfamily P.gridLabel
        (actualGPrimeLabelFirstLeftIndex_mem_family
          N D keep left right ballRadius omega a)
  have htranslate := tubePairCoefficientDistance_traceTranslateTube_le_add
    (actualThreeShiftCGridLeftTube P a) globalCenter shift
  have hbase' : tubePairCoefficientDistance
      (actualThreeShiftCGridLeftTube P a) globalCenter <= 3 * tGlobal := by
    simpa only [actualThreeShiftCGridLeftTube] using hbase
  exact htranslate.trans (by linarith [hbase'])

/-- The final right endpoint is untranslated and retains the exact original
global-norm radius. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedRightTube_distance_le
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (a : Survivor N D keep left right ballRadius omega) :
    tubePairCoefficientDistance
        (actualThreeShiftCGridRestrictedRightTube P a) globalCenter <=
      3 * tGlobal := by
  exact threeShiftCGridNormalizeTube_distance_le_three_mul_of_mem_family
    fine physical tGlobal globalCenter N D hDfine hfamily P.gridLabel
      (actualGPrimeLabelFirstRightIndex_mem_family
        N D keep left right ballRadius omega a)

/-- Uniform radius used for both final endpoint maps. -/
def actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
    (tGlobal shift : Real) : Real :=
  3 * (tGlobal + |shift|)

/-- Direct `hball` adapter for the final retained pair family.  It uses the
same maps as the restricted canonical C-fibres. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedRetainedPairTubeFamily_distance_le
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (survivors : Finset (Survivor N D keep left right ballRadius omega))
    (shift : Real) (V : Tube radius)
    (hV : V ∈ retainedPairTubeFamily survivors
      (actualThreeShiftCGridRestrictedTraceLeftTube P shift)
      (actualThreeShiftCGridRestrictedRightTube P)) :
    tubePairCoefficientDistance V globalCenter <=
      actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
        tGlobal shift := by
  simp only [retainedPairTubeFamily, Finset.mem_union,
    Finset.mem_image] at hV
  rcases hV with ⟨a, _ha, rfl⟩ | ⟨a, _ha, rfl⟩
  · have hleft :=
      actualGPrimeLabelFirstThreeShiftCGridRestrictedTraceLeftTube_distance_le
        fine physical tGlobal globalCenter N D keep left right ballRadius
          omega P hDfine hfamily shift a
    dsimp only [
      actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius]
    linarith [abs_nonneg shift]
  · have hright :=
      actualGPrimeLabelFirstThreeShiftCGridRestrictedRightTube_distance_le
        fine physical tGlobal globalCenter N D keep left right ballRadius
          omega P hDfine hfamily a
    dsimp only [
      actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius]
    linarith [abs_nonneg shift]

/-- Equivalent adapter on the deduplicated global carrier used for the
lossless outer C-fibre sum. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_distance_le
    (hDfine : D.fine = fine)
    (hfamily : N.family =
      actualGlobalNormIndexFamily fine physical tGlobal globalCenter)
    (survivors : Finset (Survivor N D keep left right ballRadius omega))
    (shift : Real) (V : Tube radius)
    (hV : V ∈ actualThreeShiftCGridRestrictedGlobalTubeFamily
      P survivors shift) :
    tubePairCoefficientDistance V globalCenter <=
      actualGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientRadius
        tGlobal shift := by
  apply
    actualGPrimeLabelFirstThreeShiftCGridRestrictedRetainedPairTubeFamily_distance_le
      fine physical tGlobal globalCenter N D keep left right ballRadius omega
        P hDfine hfamily survivors shift V
  simpa only [actualThreeShiftCGridRestrictedGlobalTubeFamily,
    FamilyStickyCinematicL32FiniteValuePairCarrierV1.finitePairCarrier,
    retainedPairTubeFamily] using hV

end Ball

#print axioms threeShiftCGridNormalizeTube_distance_le_three_mul_of_mem_family
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedTraceLeftTube_distance_le
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedRightTube_distance_le
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedRetainedPairTubeFamily_distance_le
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_distance_le

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedCoefficientBallV1
