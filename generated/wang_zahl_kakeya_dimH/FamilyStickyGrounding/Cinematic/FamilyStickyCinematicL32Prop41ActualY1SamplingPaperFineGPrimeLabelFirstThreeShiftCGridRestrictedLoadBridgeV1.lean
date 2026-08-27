import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedLoadBridgeV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridSelectionV1
open FamilyStickyCinematicL32Prop41ActualY1RetainedThreeShiftCGridRestrictedCanonicalFibresV1

noncomputable section

local instance tubeDecidableEq {radius : NNReal} :
    DecidableEq (Tube radius) := Classical.decEq _

universe u v

section Load

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {fineLabel : Type v} [DecidableEq fineLabel]
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

/-- Every actual label-first left index comes from the left zero-colour
sample.  Passing to values can only decrease cardinality. -/
theorem actualGPrimeLabelFirst_leftIndex_image_card_le_zeroColorSample
    (survivors : Finset (Survivor N D keep left right ballRadius omega)) :
    (survivors.image (actualGPrimeLabelFirstLeftIndex
      N D keep left right ballRadius omega)).card <=
      (zeroColorSample 1 omega.1).card := by
  classical
  let sampleIndices : Finset iota :=
    (zeroColorSample 1 omega.1).image (fun i : N.family => i.1)
  have hsub : survivors.image (actualGPrimeLabelFirstLeftIndex
      N D keep left right ballRadius omega) ⊆ sampleIndices := by
    intro i hi
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hi
    let hit := survivorLeftHitWitness 1 1
      (leftNeighbors N D keep left right ballRadius)
      (rightNeighbors N D keep left right ballRadius) omega a
    apply Finset.mem_image.mpr
    refine ⟨hit.1, ?_, ?_⟩
    · simp only [zeroColorSample, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact hit.2.2
    · rfl
  calc
    _ <= sampleIndices.card := Finset.card_le_card hsub
    _ <= (zeroColorSample 1 omega.1).card := Finset.card_image_le

/-- Every actual label-first right index comes from the right zero-colour
sample. -/
theorem actualGPrimeLabelFirst_rightIndex_image_card_le_zeroColorSample
    (survivors : Finset (Survivor N D keep left right ballRadius omega)) :
    (survivors.image (actualGPrimeLabelFirstRightIndex
      N D keep left right ballRadius omega)).card <=
      (zeroColorSample 1 omega.2).card := by
  classical
  let sampleIndices : Finset iota :=
    (zeroColorSample 1 omega.2).image (fun i : N.family => i.1)
  have hsub : survivors.image (actualGPrimeLabelFirstRightIndex
      N D keep left right ballRadius omega) ⊆ sampleIndices := by
    intro i hi
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hi
    let hit := survivorRightHitWitness 1 1
      (leftNeighbors N D keep left right ballRadius)
      (rightNeighbors N D keep left right ballRadius) omega a
    apply Finset.mem_image.mpr
    refine ⟨hit.1, ?_, ?_⟩
    · simp only [zeroColorSample, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact hit.2.2
    · rfl
  calc
    _ <= sampleIndices.card := Finset.card_le_card hsub
    _ <= (zeroColorSample 1 omega.2).card := Finset.card_image_le

variable {items : Finset (Survivor N D keep left right ballRadius omega)}
variable {pairScale : Real}
variable (P : ActualRetainedY1ThreeShiftCGridSelection D items
  (actualGPrimeLabelFirstLeftIndex N D keep left right ballRadius omega)
  (actualGPrimeLabelFirstRightIndex N D keep left right ballRadius omega)
  (actualGPrimeLabelFirstLabel N D keep left right ballRadius omega)
  keep pairScale)

/-- The final trace-shifted, grid-normalised endpoint carrier is bounded by
the two original zero-colour samples.  No pair multiplicity or C-fibre
multiplicity enters this estimate. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_card_le_sample_cards
    (survivors : Finset (Survivor N D keep left right ballRadius omega))
    (shift : Real) :
    (actualThreeShiftCGridRestrictedGlobalTubeFamily P survivors shift).card <=
      (zeroColorSample 1 omega.1).card +
        (zeroColorSample 1 omega.2).card := by
  calc
    _ <= (survivors.image (actualGPrimeLabelFirstLeftIndex
          N D keep left right ballRadius omega)).card +
        (survivors.image (actualGPrimeLabelFirstRightIndex
          N D keep left right ballRadius omega)).card :=
      actualThreeShiftCGridRestrictedGlobalTubeFamily_card_le_index_images
        P survivors shift
    _ <= (zeroColorSample 1 omega.1).card +
        (zeroColorSample 1 omega.2).card :=
      Nat.add_le_add
        (actualGPrimeLabelFirst_leftIndex_image_card_le_zeroColorSample
          N D keep left right ballRadius omega survivors)
        (actualGPrimeLabelFirst_rightIndex_image_card_le_zeroColorSample
          N D keep left right ballRadius omega survivors)

/-- Real-valued form used by the automatic depth and curve-budget APIs. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_card_cast_le_load
    (survivors : Finset (Survivor N D keep left right ballRadius omega))
    (shift : Real) :
    ((actualThreeShiftCGridRestrictedGlobalTubeFamily
      P survivors shift).card : Real) <= twoSidedZeroColorLoad 1 1 omega := by
  have hcard :=
    actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_card_le_sample_cards
      N D keep left right ballRadius omega P survivors shift
  unfold twoSidedZeroColorLoad
  exact_mod_cast hcard

/-- Lossless outer C-fibre summation followed by the same original load
bound.  This is the form needed by an all-fibre aggregator. -/
theorem actualGPrimeLabelFirstThreeShiftCGridRestricted_sum_tubeFiber_card_cast_le_load
    {survivors : Finset (Survivor N D keep left right ballRadius omega)}
    (hsub : survivors ⊆ P.selected) (shift : Real) :
    ((∑ c ∈ actualThreeShiftCGridRestrictedOccupiedValues P survivors shift,
        (actualThreeShiftCGridRestrictedTubeFamilyAt
          P survivors shift c).card : Nat) : Real) <=
      twoSidedZeroColorLoad 1 1 omega := by
  rw [← actualThreeShiftCGridRestrictedGlobalTubeFamily_card_eq_sum_fiber_card
    P hsub shift]
  exact
    actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_card_cast_le_load
      N D keep left right ballRadius omega P survivors shift

end Load

#print axioms actualGPrimeLabelFirst_leftIndex_image_card_le_zeroColorSample
#print axioms actualGPrimeLabelFirst_rightIndex_image_card_le_zeroColorSample
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestrictedGlobalTubeFamily_card_cast_le_load
#print axioms actualGPrimeLabelFirstThreeShiftCGridRestricted_sum_tubeFiber_card_cast_le_load

end

end FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstThreeShiftCGridRestrictedLoadBridgeV1
