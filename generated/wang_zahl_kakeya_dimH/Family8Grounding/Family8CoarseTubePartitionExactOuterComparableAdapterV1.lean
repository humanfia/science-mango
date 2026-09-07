import Family8Grounding.Family8ExactOuterComparableActualAverageMassDensityV1
import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Mathlib.Tactic

/-!
# Coarse-tube-partition adapter for the exact-outer comparable assembly

This adapter keeps the literal `CoarseTubePartition`, all actual-average and
mass/density outputs, and the exact induced-outer identity on the same final
refinement.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoarseTubePartitionExactOuterComparableAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ComparableMultiplicityBucketsV1
open Family8ExactOuterComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1

noncomputable section

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa] [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- The scale-aware partition is definitionally compatible with the exact
outer assembly, including its induced-shading identity. -/
theorem exists_exactOuter_frozenComparableAssembly_of_coarseTubePartition
    (P : CoarseTubePartition fine coarse)
    (Y : Shading fine.bodyFamily) (r : Real) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y P.fineIndices).shading.shadingMass ≠
        0) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        P.asConvexFactorization Y r,
      A.loss = frozenComparableLoss iota kappa ∧
      A.fiberLabel ∈ Finset.range (Nat.log 2 (Fintype.card iota) + 2) ∧
      A.outerLabel ∈ Finset.range (Nat.log 2 (Fintype.card kappa) + 2) ∧
      A.frozenCoarse =
        P.asConvexFactorization.inducedShading A.refinement.shading ∧
      (sourceActiveFineShading P.asConvexFactorization Y).shadingMass ≤
        (frozenComparableLoss iota kappa : ENNReal) *
          (actualRefinementShading A).shadingMass ∧
      (sourceActiveFineShading P.asConvexFactorization Y).shadingDensity /
          (frozenComparableLoss iota kappa : ENNReal) ≤
        (actualRefinementShading A).shadingDensity ∧
      ∃ k ∈ P.coarseIndices,
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
  have hsource' :
      (IndexedShadingRefinement.restrictTo Y
        P.asConvexFactorization.index.fine).shading.shadingMass ≠ 0 := by
    simpa [CoarseTubePartition.fineIndices,
      CoarseTubePartition.asConvexFactorization] using hsource
  simpa [CoarseTubePartition.coarseIndices,
    CoarseTubePartition.asConvexFactorization] using
    (exists_exactOuter_frozenComparableAssembly_with_actualAverages_mass_density
      P.asConvexFactorization Y r hr hsource')

#print axioms
  exists_exactOuter_frozenComparableAssembly_of_coarseTubePartition

end
end Family8CoarseTubePartitionExactOuterComparableAdapterV1
