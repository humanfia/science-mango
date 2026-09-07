import Family8Grounding.Family8ExactOuterComparableActualAverageMassDensityV1
import Family8Grounding.Family8SelectedOccurrenceDensityFrostmanV1
import Family8Grounding.Family8SelectedOccurrenceFineBucketSupportV1
import Mathlib.Tactic

/-!
# Polylogarithmic exact-outer payload on selected occurrences

Starting from a fine-index bucket supported on the selected occurrence fibres,
this module applies the exact-outer frozen-comparable producer directly to the
selected factorization.  The coarse witness returned by that same producer is
decoded through the literal `Option.some` image of `R`; no second occurrence is
selected.

Only the polylogarithmic loss identity, exact outer identity, positive final
fibre, and actual-average product needed downstream are retained.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceExactOuterFrozenComparablePayloadV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Family8ExactOuterComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFineBucketSupportV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset iota}

/-- A selected fine bucket admits the polylogarithmic exact-outer frozen
assembly, with the producer's own coarse witness decoded as the unique
retained occurrence label `q`. -/
theorem exists_selectedOccurrence_exactOuter_frozenComparable_payload
    (P : GreedyDensityPartition F candidates container active)
    (R : Finset (Fin (blocks F P).length)) (Y : Shading F)
    (fineBucket : Finset iota)
    (hfineBucket : fineBucket ⊆ selectedOccurrenceFineIndices P R)
    (hYbucket :
      (IndexedShadingRefinement.restrictTo Y fineBucket).shading.shadingMass ≠
        0)
    (r : Real) (hr : 0 < r) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (selectedOccurrenceFactorization P R)
        (IndexedShadingRefinement.restrictTo Y fineBucket).shading r,
      A.loss = frozenComparableLoss iota
          (Option (Fin (blocks F P).length)) ∧
      A.frozenCoarse =
          (selectedOccurrenceFactorization P R).inducedShading
            A.refinement.shading ∧
      ∃ q ∈ R,
        0 < volume
          (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
            A (some q)).shadedUnion ∧
        (Family8FrozenComparableActualAverageMassDensityV1.Assembly.actualRefinementShading
            A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
              A (some q)).averageMultiplicity) := by
  classical
  let Q := selectedOccurrenceFactorization P R
  let Ybucket :=
    (IndexedShadingRefinement.restrictTo Y fineBucket).shading
  have hrestrict :
      (IndexedShadingRefinement.restrictTo Ybucket Q.index.fine).shading =
        Ybucket := by
    simpa only [Q, Ybucket] using
      (selectedOccurrenceFineBucket_restrictTo_fine_eq
        P R Y fineBucket hfineBucket)
  have hsource :
      (IndexedShadingRefinement.restrictTo Ybucket Q.index.fine).shading.shadingMass ≠
        0 := by
    rw [hrestrict]
    exact hYbucket
  obtain ⟨A, hLoss, _hFiberLabel, _hOuterLabel, hExactOuter,
      _hMass, _hDensity, k, hk, hvolume, _hFiberLower, _hFiberUpper,
      _hOuterLower, _hOuterUpper, hproduct⟩ :=
    exists_exactOuter_frozenComparableAssembly_with_actualAverages_mass_density
      Q Ybucket r hr hsource
  have hkSelected : k ∈ selectedOccurrenceIndices P R := by
    simpa only [Q, selectedOccurrenceFactorization_coarse] using hk
  obtain ⟨q, hq, hqk⟩ :=
    (mem_selectedOccurrenceIndices P R k).1 hkSelected
  subst k
  refine ⟨A, ?_, ?_, q, hq, ?_, ?_⟩
  · simpa only [Q, Ybucket] using hLoss
  · simpa only [Q, Ybucket] using hExactOuter
  · simpa only [Q, Ybucket] using hvolume
  · simpa only [Q, Ybucket] using hproduct

#print axioms exists_selectedOccurrence_exactOuter_frozenComparable_payload

end

end Family8SelectedOccurrenceExactOuterFrozenComparablePayloadV1
