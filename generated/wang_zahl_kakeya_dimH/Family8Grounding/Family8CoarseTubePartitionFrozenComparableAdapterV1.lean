import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Submission.Kakeya.ConvexFactoring.CoarseTubePartition
import Mathlib.Tactic

/-!
# Coarse-tube-partition adapter for the polylogarithmic frozen assembly

The logarithmic-branching almost-cover construction outputs a genuine
`CoarseTubePartition`.  This file records the exact compatibility seam: its
`asConvexFactorization` can be fed directly to the collision-free frozen
dyadic producer, with the source and surviving parent sets identified with
the partition's actual `fineIndices` and `coarseIndices`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CoarseTubePartitionFrozenComparableAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance family8CoarseAdapterPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {delta rho : NNReal} {iota kappa : Type*}
  [Fintype iota] [Fintype kappa] [DecidableEq iota] [DecidableEq kappa]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho kappa}

/-- A scale-aware `CoarseTubePartition` produced upstream is definitionally
compatible with the polylogarithmic same-data assembly.  No almost-cover or
branching estimate is repeated as an assumption here: those remain certified
properties of the given partition and its upstream producer. -/
theorem exists_frozenComparableAssembly_of_coarseTubePartition
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
      (Assembly.sourceActiveFineShading P.asConvexFactorization Y).shadingMass ≤
        (frozenComparableLoss iota kappa : ENNReal) *
          (Assembly.actualRefinementShading A).shadingMass ∧
      (Assembly.sourceActiveFineShading P.asConvexFactorization Y).shadingDensity /
          (frozenComparableLoss iota kappa : ENNReal) ≤
        (Assembly.actualRefinementShading A).shadingDensity ∧
      ∃ k ∈ P.coarseIndices,
        0 < volume (Assembly.finalFiberShading A k).shadedUnion ∧
        (comparableBase A.fiberLabel : ENNReal) ≤
          (Assembly.finalFiberShading A k).averageMultiplicity ∧
        (Assembly.finalFiberShading A k).averageMultiplicity ≤
          (2 * comparableBase A.fiberLabel : Nat) ∧
        (comparableBase A.outerLabel : ENNReal) ≤
          A.frozenCoarse.averageMultiplicity ∧
        A.frozenCoarse.averageMultiplicity ≤
          (2 * comparableBase A.outerLabel : Nat) ∧
        (Assembly.actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (Assembly.finalFiberShading A k).averageMultiplicity) := by
  have hsource' :
      (IndexedShadingRefinement.restrictTo Y
        P.asConvexFactorization.index.fine).shading.shadingMass ≠ 0 := by
    simpa [CoarseTubePartition.fineIndices,
      CoarseTubePartition.asConvexFactorization] using hsource
  simpa [CoarseTubePartition.coarseIndices,
    CoarseTubePartition.asConvexFactorization] using
    (exists_frozenComparableAssembly_with_actualAverages_mass_density
      P.asConvexFactorization Y r hr hsource')

#print axioms exists_frozenComparableAssembly_of_coarseTubePartition

end


end Family8CoarseTubePartitionFrozenComparableAdapterV1
