import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Mathlib.Tactic

/-!
# Supported source-active-fine average reindexing

The frozen-comparable API represents its source shading on the literal
subtype of active fine indices.  If the ambient-index shading is already
empty off that active set, this change of index preserves its scalar mass,
shaded union, and hence its actual average multiplicity.

Only scalar and set identities are exposed.  In particular, no equality of
shadings with different index types is asserted.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SupportedSourceActiveFineAverageReindexV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}

private theorem sourceActiveFineShading_shadingMass_eq_of_support
    (Q : ConvexFactorization F W) (Z : Shading F)
    (hsupport : forall i, i ∉ Q.index.fine -> Z.carrier i = ∅) :
    (sourceActiveFineShading Q Z).shadingMass = Z.shadingMass := by
  classical
  rw [sourceActiveFineShading_shadingMass,
    shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hiFine
  rw [hsupport i hiFine, measure_empty]

omit [Fintype iota] [Fintype kappa] in
private theorem sourceActiveFineShading_shadedUnion_eq_of_support
    (Q : ConvexFactorization F W) (Z : Shading F)
    (hsupport : forall i, i ∉ Q.index.fine -> Z.carrier i = ∅) :
    (sourceActiveFineShading Q Z).shadedUnion = Z.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i.1, by
      change x ∈ Z.carrier i.1 at hxi
      exact hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    by_cases hi : i ∈ Q.index.fine
    · exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, by
        change x ∈ Z.carrier i
        exact hxi⟩
    · rw [hsupport i hi] at hxi
      exact hxi.elim

/-- Reindexing a shading already supported on the active fine set by the
literal active-fine subtype preserves its actual average multiplicity. -/
theorem sourceActiveFineShading_averageMultiplicity_eq_of_support
    (Q : ConvexFactorization F W) (Z : Shading F)
    (hsupport : forall i, i ∉ Q.index.fine -> Z.carrier i = ∅) :
    (sourceActiveFineShading Q Z).averageMultiplicity =
      Z.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [sourceActiveFineShading_shadingMass_eq_of_support Q Z hsupport,
    sourceActiveFineShading_shadedUnion_eq_of_support Q Z hsupport]

#print axioms sourceActiveFineShading_averageMultiplicity_eq_of_support

end

end Family8SupportedSourceActiveFineAverageReindexV1
