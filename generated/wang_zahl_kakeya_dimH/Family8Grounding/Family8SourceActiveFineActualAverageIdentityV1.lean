import Family8Grounding.Family8FrozenComparableSourceAverageRetentionV2
import Mathlib.Tactic

/-!
# Literal source-active average for the frozen comparable assembly

The frozen assembly names the source active family as a subtype, whereas the
scale-cover and property interfaces name the same data as an ambient-index
`IndexedShadingRefinement.restrictTo`.  This file proves that their shaded
unions, masses, and hence average multiplicities are literally identical.

Combining this identity with the canonical same-data retention theorem gives
an average-multiplicity comparison from the actual ambient restriction to the
actual final refinement.  No nonzero-volume premise and no analytic estimate
is introduced.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SourceActiveFineActualAverageIdentityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenComparableSourceAverageRetentionV2.SourceAverage

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

local instance family8SourceActiveAveragePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- Passing from the ambient active restriction to its literal subtype does
not change the shaded union. -/
theorem sourceActiveFineShading_shadedUnion_eq_restrictTo
    (P : ConvexFactorization F W) (Y : Shading F) :
    (sourceActiveFineShading P Y).shadedUnion =
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨i.1, ?_⟩
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos i.2]
    exact hxi
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [IndexedShadingRefinement.restrictTo_carrier] at hxi
    by_cases hi : i ∈ P.index.fine
    · rw [if_pos hi] at hxi
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
    · rw [if_neg hi] at hxi
      exact hxi.elim

/-- The subtype source shading and the literal ambient restriction have the
same actual average multiplicity, including in the zero-volume case. -/
theorem sourceActiveFineShading_averageMultiplicity_eq_restrictTo
    (P : ConvexFactorization F W) (Y : Shading F) :
    (sourceActiveFineShading P Y).averageMultiplicity =
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [sourceActiveFineShading_shadingMass,
    sourceActiveFineShading_shadedUnion_eq_restrictTo]

/-- Canonical average retention stated directly on the ambient-index active
restriction consumed by the scale-cover/property interfaces. -/
theorem restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (IndexedShadingRefinement.restrictTo Y
      P.index.fine).shading.averageMultiplicity ≤
      (A.loss : ENNReal) * (actualRefinementShading A).averageMultiplicity := by
  rw [← sourceActiveFineShading_averageMultiplicity_eq_restrictTo P Y]
  exact sourceActiveFineShading_averageMultiplicity_le_loss_mul_actualRefinement A

#print axioms sourceActiveFineShading_shadedUnion_eq_restrictTo
#print axioms sourceActiveFineShading_averageMultiplicity_eq_restrictTo
#print axioms
  restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement

end

end Family8SourceActiveFineActualAverageIdentityV1
