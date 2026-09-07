import Family8Grounding.Family8ExactOuterComparableAssemblyV2
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1

/-!
# Exact-outer comparable assembly with actual averages, mass, and density

This is the exact-outer successor of the generic frozen-comparable producer.
It keeps every actual mass, density, positive-fibre, and same-product field,
and additionally preserves the literal identity
`A.frozenCoarse = P.inducedShading A.refinement.shading`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ExactOuterComparableActualAverageMassDensityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8ComparableMultiplicityBucketsV1
open Family8ExactOuterComparableAssemblyV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}

/-- The exact induced outer shading can replace the independently frozen
outer bucket without changing the polylogarithmic loss or any downstream
actual-average field. -/
theorem exists_exactOuter_frozenComparableAssembly_with_actualAverages_mass_density
    (P : ConvexFactorization F W) (Y : Shading F)
    (r : Real) (_hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadingMass ≠
        0) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r,
      A.loss = frozenComparableLoss iota kappa ∧
      A.fiberLabel ∈ Finset.range (Nat.log 2 (Fintype.card iota) + 2) ∧
      A.outerLabel ∈ Finset.range (Nat.log 2 (Fintype.card kappa) + 2) ∧
      A.frozenCoarse = P.inducedShading A.refinement.shading ∧
      (sourceActiveFineShading P Y).shadingMass ≤
        (frozenComparableLoss iota kappa : ENNReal) *
          (actualRefinementShading A).shadingMass ∧
      (sourceActiveFineShading P Y).shadingDensity /
          (frozenComparableLoss iota kappa : ENNReal) ≤
        (actualRefinementShading A).shadingDensity ∧
      ∃ k ∈ P.index.coarse,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (comparableBase A.fiberLabel : ENNReal) ≤
          (finalFiberShading A k).averageMultiplicity ∧
        (finalFiberShading A k).averageMultiplicity ≤
          (2 * comparableBase A.fiberLabel : Nat) ∧
        (comparableBase A.outerLabel : ENNReal) ≤
          A.frozenCoarse.averageMultiplicity ∧
        A.frozenCoarse.averageMultiplicity ≤
          (2 * comparableBase A.outerLabel : Nat) ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  obtain ⟨A, hLoss, hFiberLabel, hOuterLabel, hExactOuter⟩ :=
    exists_exactOuter_assembly P Y r
  have hmass :=
    sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
  have hdensity :=
    sourceActiveFineShading_density_div_loss_le_actualRefinementShading A
  obtain ⟨k, hk, hfiber, _hrefinement, houter⟩ :=
    Assembly.exists_positive_finalFiber A hsource
  have hfiberLower :=
    finalFiberShading_averageMultiplicity_lower A k hk (ne_of_gt hfiber)
  have hfiberUpper :=
    finalFiberShading_averageMultiplicity_upper A k hk
  have houterLower :=
    frozenCoarse_averageMultiplicity_lower A (ne_of_gt houter)
  have houterUpper := frozenCoarse_averageMultiplicity_upper A
  have hproduct :=
    refinement_averageMultiplicity_le_four_mul_actualAverages
      A k hk (ne_of_gt hfiber) (ne_of_gt houter)
  have hactualProduct :
      (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity) := by
    rw [actualRefinementShading_averageMultiplicity]
    exact hproduct
  refine ⟨A, ?_, hFiberLabel, hOuterLabel, hExactOuter, ?_, ?_,
    k, hk, hfiber, hfiberLower, hfiberUpper, houterLower, houterUpper,
    hactualProduct⟩
  · simpa only [frozenComparableLoss] using hLoss
  · simpa only [hLoss, frozenComparableLoss] using hmass
  · simpa only [hLoss, frozenComparableLoss] using hdensity

#print axioms
  exists_exactOuter_frozenComparableAssembly_with_actualAverages_mass_density

end
end Family8ExactOuterComparableActualAverageMassDensityV1
