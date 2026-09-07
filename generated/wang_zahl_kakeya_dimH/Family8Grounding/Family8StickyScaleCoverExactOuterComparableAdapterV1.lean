import Family8Grounding.Family8CoarseTubePartitionExactOuterComparableAdapterV1
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2

/-!
# Sticky-cover adapter for the exact-outer comparable assembly

The literal source-mass partition of a Sticky cover is fed to the clean
exact-outer coarse-partition producer.  All old actual-data conclusions are
retained together with the exact induced outer shading identity.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyScaleCoverExactOuterComparableAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open Family8CoarseTubePartitionExactOuterComparableAdapterV1
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8StickyScaleCoverFrozenComparableAdapterV2

noncomputable section

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- A Sticky cover with nonzero active source mass produces the exact-outer
assembly on the same source-mass partition. -/
theorem exists_exactOuter_frozenComparableAssembly_of_stickyScaleCover
    (S : StickyScaleCover fine rho) (hscale : delta ≤ rho)
    (Y : Shading fine.bodyFamily) (r : Real) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass ≠
        0) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
          Y r,
      A.loss = frozenComparableLoss iota (Fin S.coarseCard) ∧
      A.fiberLabel ∈ Finset.range (Nat.log 2 (Fintype.card iota) + 2) ∧
      A.outerLabel ∈
        Finset.range (Nat.log 2 (Fintype.card (Fin S.coarseCard)) + 2) ∧
      A.frozenCoarse =
        (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization.inducedShading
          A.refinement.shading ∧
      (sourceActiveFineShading
          (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
          Y).shadingMass ≤
        (frozenComparableLoss iota (Fin S.coarseCard) : ENNReal) *
          (actualRefinementShading A).shadingMass ∧
      (sourceActiveFineShading
          (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
          Y).shadingDensity /
          (frozenComparableLoss iota (Fin S.coarseCard) : ENNReal) ≤
        (actualRefinementShading A).shadingDensity ∧
      ∃ k ∈ S.activeCoarse,
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
  simpa [sourceMassCoarseTubePartition] using
    (exists_exactOuter_frozenComparableAssembly_of_coarseTubePartition
      (sourceMassCoarseTubePartition S hscale Y hsource) Y r hr
      (by simpa using hsource))

#print axioms
  exists_exactOuter_frozenComparableAssembly_of_stickyScaleCover

end
end Family8StickyScaleCoverExactOuterComparableAdapterV1
