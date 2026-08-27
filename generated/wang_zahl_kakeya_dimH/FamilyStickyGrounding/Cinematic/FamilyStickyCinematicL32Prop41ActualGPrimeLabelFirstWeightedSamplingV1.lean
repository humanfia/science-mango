import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRandomSamplingWeightedExtractionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSamplingV1

open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberRandomSamplingV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingWeightedExtractionV1

noncomputable section

universe u v

/-!
# Weight-aware actual G-prime label-first sampling

This is the actual-carrier specialization of the package-free weighted
zero-colour theorem.  The random outcome is chosen using the supplied label
weight; it is therefore intentionally a new outcome rather than a property
asserted after the old cardinal-maximizing choice.
-/

/-- Sum over the survivor subtype equals the corresponding sum over the
literal survivor finset. -/
theorem actualGPrimeLabelFirstSurvivor_weight_sum_eq
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (labelWeight : fineLabel -> ENNReal) :
    (∑ S : ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega,
      labelWeight (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega S)) =
      ∑ r ∈ twoSidedZeroColorSurvivors 1 1
        (fun r : actualGPrimeBilateralRetainedFineLabels
            N D keep left right ballRadius =>
          actualGPrimeRetainedFineMetricNeighbors
            N D keep left ballRadius r.1)
        (fun r : actualGPrimeBilateralRetainedFineLabels
            N D keep left right ballRadius =>
          actualGPrimeRetainedFineMetricNeighbors
            N D keep right ballRadius r.1)
        omega,
        labelWeight r.1 := by
  exact Finset.sum_attach
    (twoSidedZeroColorSurvivors 1 1
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r.1)
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r.1)
      omega)
    (fun r => labelWeight r.1)

/-- The weight-aware sampled outcome used by the downstream grid and trace
selections. -/
structure ActualGPrimeLabelFirstWeightedSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (labelWeight : fineLabel -> ENNReal)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) : Prop where
  weighted_survival :
    (∑ r ∈ actualGPrimeBilateralRetainedFineLabels
        N D keep left right ballRadius, labelWeight r) / 8 <=
      ∑ S : ActualGPrimeLabelFirstSurvivor
        N D keep left right ballRadius omega,
        labelWeight (actualGPrimeLabelFirstLabel
          N D keep left right ballRadius omega S)
  load : twoSidedZeroColorLoad 1 1 omega <=
    7 * ((N.family.card : Real) / (1 : Real) +
      (N.family.card : Real) / (1 : Real))
  retained_tube_card_le_load :
    ((survivorRetainedPairTubeFamily 1 1
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep left ballRadius r.1)
      (fun r : actualGPrimeBilateralRetainedFineLabels
          N D keep left right ballRadius =>
        actualGPrimeRetainedFineMetricNeighbors
          N D keep right ballRadius r.1)
      omega (fun i : N.family => D.fine.tubes i.1)
        (fun i : N.family => D.fine.tubes i.1)).card : Real) <=
      twoSidedZeroColorLoad 1 1 omega

/-- Choose one actual label-first random sample which simultaneously retains
one eighth of arbitrary `ENNReal` label weight and obeys the old sevenfold
load estimate. -/
theorem exists_actualGPrimeLabelFirstWeightedSampledOutcome
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real) (labelWeight : fineLabel -> ENNReal) :
    exists omega : (N.family -> Fin 1) × (N.family -> Fin 1),
      ActualGPrimeLabelFirstWeightedSampledOutcome N D keep left right
        ballRadius labelWeight omega := by
  classical
  let labels := actualGPrimeBilateralRetainedFineLabels
    N D keep left right ballRadius
  let leftNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep left ballRadius r.1
  let rightNeighbors : labels -> Finset N.family := fun r =>
    actualGPrimeRetainedFineMetricNeighbors
      N D keep right ballRadius r.1
  have hleft : forall r : labels, 1 <= (leftNeighbors r).card := by
    intro r
    apply Finset.one_le_card.mpr
    exact ((mem_actualGPrimeBilateralRetainedFineLabels_iff
      N D keep left right ballRadius r.1).mp r.2).2.1
  have hright : forall r : labels, 1 <= (rightNeighbors r).card := by
    intro r
    apply Finset.one_le_card.mpr
    exact ((mem_actualGPrimeBilateralRetainedFineLabels_iff
      N D keep left right ballRadius r.1).mp r.2).2.2
  obtain ⟨omega, hsurvival, hload⟩ :=
    exists_twoSidedZeroColor_sample_with_eighth_ennrealWeight_and_sevenfold_load
      (Rectangle := labels) (alpha := N.family) (beta := N.family)
      1 1 leftNeighbors rightNeighbors (fun r => labelWeight r.1)
        hleft hright
  refine ⟨omega, {
    weighted_survival := ?_
    load := ?_
    retained_tube_card_le_load := ?_ }⟩
  · rw [actualGPrimeLabelFirstSurvivor_weight_sum_eq]
    simpa only [labels, leftNeighbors, rightNeighbors,
      Finset.sum_attach, Finset.univ_eq_attach] using hsurvival
  · simpa only [Nat.cast_one, Fintype.card_coe] using hload
  · exact survivorRetainedPairTubeFamily_card_cast_le_load 1 1
      leftNeighbors rightNeighbors omega
      (fun i : N.family => D.fine.tubes i.1)
      (fun i : N.family => D.fine.tubes i.1)

#print axioms actualGPrimeLabelFirstSurvivor_weight_sum_eq
#print axioms ActualGPrimeLabelFirstWeightedSampledOutcome
#print axioms exists_actualGPrimeLabelFirstWeightedSampledOutcome

end

end FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstWeightedSamplingV1
