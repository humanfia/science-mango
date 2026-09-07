import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Mathlib.Tactic

/-!
# Support identity for a selected-occurrence fine bucket

A fine-index bucket already contained in the active fine set of the
selected-occurrence factorization is unchanged by restricting it to that
active set once more.  This is the exact support seam needed before running
an exact-outer assembly on the whole retained occurrence bucket.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFineBucketSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- Proof fields of a shading are irrelevant, so equality of its carrier
function determines the whole structure. -/
theorem shading_eq_of_carrier_eq
    {j : Type*} {G : ConvexFamily j}
    (Y Z : Shading G) (hcarrier : Y.carrier = Z.carrier) : Y = Z := by
  cases Y
  cases Z
  simpa only [Shading.mk.injEq] using hcarrier

/-- Restricting a shading to a set outside which it is already empty is
literally the same shading. -/
theorem restrictTo_eq_self_of_carrier_eq_empty_of_not_mem
    {j : Type*} [DecidableEq j] {G : ConvexFamily j}
    (Z : Shading G) (s : Finset j)
    (hsupport : forall i, i ∉ s -> Z.carrier i = ∅) :
    (IndexedShadingRefinement.restrictTo Z s).shading = Z := by
  apply shading_eq_of_carrier_eq
  funext i
  rw [IndexedShadingRefinement.restrictTo_carrier]
  by_cases hi : i ∈ s
  · rw [if_pos hi]
  · rw [if_neg hi, hsupport i hi]

/-- A restriction to `fineBucket` is supported on the selected-occurrence
factorization whenever that bucket lies in the selected fine union. -/
theorem selectedOccurrenceFineBucket_carrier_eq_empty_of_not_fine
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (Y : Shading F) (fineBucket : Finset iota)
    (hfineSubset :
      fineBucket ⊆ selectedOccurrenceFineIndices P R)
    (i : iota)
    (hi : i ∉ (selectedOccurrenceFactorization P R).index.fine) :
    (IndexedShadingRefinement.restrictTo
      Y fineBucket).shading.carrier i = ∅ := by
  classical
  have hiBucket : i ∉ fineBucket := by
    intro hiFineBucket
    apply hi
    rw [selectedOccurrenceFactorization_fine P R]
    exact hfineSubset hiFineBucket
  rw [IndexedShadingRefinement.restrictTo_carrier, if_neg hiBucket]

/-- The retained bucket is unchanged by the active-fine restriction of the
selected-occurrence factorization. -/
theorem selectedOccurrenceFineBucket_restrictTo_fine_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (Y : Shading F) (fineBucket : Finset iota)
    (hfineSubset :
      fineBucket ⊆ selectedOccurrenceFineIndices P R) :
    (IndexedShadingRefinement.restrictTo
      (IndexedShadingRefinement.restrictTo Y fineBucket).shading
      (selectedOccurrenceFactorization P R).index.fine).shading =
        (IndexedShadingRefinement.restrictTo Y fineBucket).shading := by
  classical
  apply restrictTo_eq_self_of_carrier_eq_empty_of_not_mem
  exact selectedOccurrenceFineBucket_carrier_eq_empty_of_not_fine
    P R Y fineBucket hfineSubset

/-- Mass is unchanged by the redundant selected-occurrence active-fine
restriction. -/
theorem selectedOccurrenceFineBucket_restrictTo_fine_shadingMass_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (Y : Shading F) (fineBucket : Finset iota)
    (hfineSubset :
      fineBucket ⊆ selectedOccurrenceFineIndices P R) :
    (IndexedShadingRefinement.restrictTo
      (IndexedShadingRefinement.restrictTo Y fineBucket).shading
      (selectedOccurrenceFactorization P R).index.fine).shading.shadingMass =
        (IndexedShadingRefinement.restrictTo
          Y fineBucket).shading.shadingMass := by
  rw [selectedOccurrenceFineBucket_restrictTo_fine_eq
    P R Y fineBucket hfineSubset]

/-- Actual average multiplicity is likewise unchanged, including when the
shaded union has zero volume. -/
theorem selectedOccurrenceFineBucket_restrictTo_fine_averageMultiplicity_eq
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (Y : Shading F) (fineBucket : Finset iota)
    (hfineSubset :
      fineBucket ⊆ selectedOccurrenceFineIndices P R) :
    (IndexedShadingRefinement.restrictTo
      (IndexedShadingRefinement.restrictTo Y fineBucket).shading
      (selectedOccurrenceFactorization P R).index.fine).shading.averageMultiplicity =
      (IndexedShadingRefinement.restrictTo
        Y fineBucket).shading.averageMultiplicity := by
  rw [selectedOccurrenceFineBucket_restrictTo_fine_eq
    P R Y fineBucket hfineSubset]

/-- Nonzero bucket mass is exactly the nonzero source-mass premise consumed
by the exact-outer assembly on `selectedOccurrenceFactorization P R`. -/
theorem selectedOccurrenceFineBucket_restrictTo_fine_shadingMass_ne_zero
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length))
    (Y : Shading F) (fineBucket : Finset iota)
    (hfineSubset :
      fineBucket ⊆ selectedOccurrenceFineIndices P R)
    (hbucket0 :
      (IndexedShadingRefinement.restrictTo
        Y fineBucket).shading.shadingMass ≠ 0) :
    (IndexedShadingRefinement.restrictTo
      (IndexedShadingRefinement.restrictTo Y fineBucket).shading
      (selectedOccurrenceFactorization P R).index.fine).shading.shadingMass ≠
        0 := by
  rw [selectedOccurrenceFineBucket_restrictTo_fine_shadingMass_eq
    P R Y fineBucket hfineSubset]
  exact hbucket0

#print axioms restrictTo_eq_self_of_carrier_eq_empty_of_not_mem
#print axioms selectedOccurrenceFineBucket_carrier_eq_empty_of_not_fine
#print axioms selectedOccurrenceFineBucket_restrictTo_fine_eq
#print axioms
  selectedOccurrenceFineBucket_restrictTo_fine_shadingMass_eq
#print axioms
  selectedOccurrenceFineBucket_restrictTo_fine_averageMultiplicity_eq
#print axioms
  selectedOccurrenceFineBucket_restrictTo_fine_shadingMass_ne_zero

end
end Family8SelectedOccurrenceFineBucketSupportV1
