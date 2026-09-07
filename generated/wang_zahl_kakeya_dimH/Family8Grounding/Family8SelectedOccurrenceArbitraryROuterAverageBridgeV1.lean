import Family8Grounding.Family8SelectedOccurrenceAverageRetentionV1
import Family8Grounding.Family8SelectedOccurrenceFineBucketSupportV1
import Mathlib.Tactic

/-!
# Arbitrary-selected-occurrence outer average reindex

For an arbitrary occurrence set `R`, the induced shading of
`selectedOccurrenceFactorization P R` and the attached-subtype shading
`selectedOccurrenceOuterShading P Z R` encode the same active outer
carriers.  Their index types differ, so the public interface records only
the exact actual-average identity needed downstream.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceArbitraryROuterAverageBridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family8SelectedOccurrenceAverageRetentionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFineBucketSupportV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- On the common ambient coarse index type, the selected factorization's
induced shading is exactly the full induced shading restricted to the
selected occurrence indices.  This helper is private: no equality across the
ambient and attached-subtype index types is exposed. -/
private theorem selectedOccurrenceFactorization_inducedShading_eq_refinement
    (P : GreedyDensityPartition F candidates container active)
    (Z : Shading F)
    (R : Finset (Fin (blocks F P).length)) :
    (selectedOccurrenceFactorization P R).inducedShading Z =
      (selectedOccurrenceRefinement P Z R).shading := by
  classical
  apply shading_eq_of_carrier_eq
  funext k
  unfold selectedOccurrenceRefinement
  rw [IndexedShadingRefinement.restrictTo_carrier]
  by_cases hk : k ∈ selectedOccurrenceIndices P R
  · rw [if_pos hk]
    obtain ⟨q, hq, hqk⟩ :=
      (mem_selectedOccurrenceIndices P R k).mp hk
    subst k
    have hselected :
        some q ∈ (selectedOccurrenceFactorization P R).index.coarse := by
      rw [selectedOccurrenceFactorization_coarse P R]
      exact (mem_selectedOccurrenceIndices P R (some q)).mpr
        ⟨q, hq, rfl⟩
    have hfull :
        some q ∈ (convexFactorization F P).index.coarse := by
      change some q ∈ occurrenceIndices F P
      simp [occurrenceIndices]
    have hfiber :
        (selectedOccurrenceFactorization P R).index.fiber (some q) =
          (convexFactorization F P).index.fiber (some q) := by
      calc
        (selectedOccurrenceFactorization P R).index.fiber (some q) =
            (blockAt F P q).fiber :=
          selectedOccurrenceFactorization_fiber P R q hq
        _ = (convexFactorization F P).index.fiber (some q) :=
          (indexFactorization_fiber_eq_blockAt F P q).symm
    apply Set.ext
    intro x
    rw [
      (selectedOccurrenceFactorization P R).mem_inducedShading_carrier_iff
        Z (some q) x,
      (convexFactorization F P).mem_inducedShading_carrier_iff
        Z (some q) x,
      hfiber]
    simp only [hselected, hfull, true_and]
  · rw [if_neg hk]
    simp [ConvexFactorization.inducedShading, hk]

/-- Arbitrary-`R` exact outer-average reindex.  No occurrence geometry,
density range, nonemptiness, or core-high premise is required. -/
theorem selectedOccurrenceFactorization_inducedShading_averageMultiplicity_eq_outer
    (P : GreedyDensityPartition F candidates container active)
    (Z : Shading F)
    (R : Finset (Fin (blocks F P).length)) :
    ((selectedOccurrenceFactorization P R).inducedShading Z).averageMultiplicity =
      (selectedOccurrenceOuterShading P Z R).averageMultiplicity := by
  rw [selectedOccurrenceFactorization_inducedShading_eq_refinement P Z R]
  exact selectedOccurrenceRefinement_averageMultiplicity_eq P Z R

#print axioms
  selectedOccurrenceFactorization_inducedShading_averageMultiplicity_eq_outer

end
end Family8SelectedOccurrenceArbitraryROuterAverageBridgeV1
