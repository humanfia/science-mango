import Family8Grounding.Family8CoarseTubePartitionFrozenComparableAdapterV1
import FamilyStickyGrounding.FamilyStickyScaleCoverAdjacentStepBridgeV2
import Mathlib.Tactic

/-!
# Sticky-cover adapter for the polylogarithmic frozen assembly

An actual `StickyScaleCover` already contains a literal parent map and all
carrier containments needed by `CoarseTubePartition`.  The only genuine
nondegeneracy needed by the frozen dyadic producer is that the source shading
restricted to the active fine indices has nonzero mass.  This file derives
the nonempty coarse endpoint from that mass and feeds the resulting actual
partition to the collision-free polylogarithmic assembly.

No almost-cover, `lotsOfUinW`, cover-cost, retention, or desired-average
inequality is supplied as a callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyScaleCoverFrozenComparableAdapterV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyScaleCoverAdjacentStepBridgeV2
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8CoarseTubePartitionFrozenComparableAdapterV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance family8StickyFrozenPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Nonzero mass on the literal active fine restriction forces an active fine
index.  Its actual parent, already stored in the Sticky cover, forces an
active coarse index. -/
theorem activeCoarse_nonempty_of_restricted_shadingMass_ne_zero
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass ≠
        0) :
    S.activeCoarse.Nonempty := by
  have hfine : S.activeFine.Nonempty := by
    by_contra hnot
    have hempty : S.activeFine = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    apply hsource
    rw [shadingMass_restrictTo_eq_sum, hempty]
    simp
  obtain ⟨i, hi⟩ := hfine
  exact ⟨S.parent i, S.parent_mem i hi⟩

/-- The actual coarse partition determined by a Sticky cover and a nonzero
active source shading.  Its proof argument records only necessary
nondegeneracy; all parent and containment data are copied from `S`. -/
def sourceMassCoarseTubePartition
    (S : StickyScaleCover fine rho) (hscale : delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass ≠
        0) :
    CoarseTubePartition fine S.coarse :=
  toCoarseTubePartition S hscale
    (activeCoarse_nonempty_of_restricted_shadingMass_ne_zero S Y hsource)

@[simp] theorem sourceMassCoarseTubePartition_fineIndices
    (S : StickyScaleCover fine rho) (hscale : delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass ≠
        0) :
    (sourceMassCoarseTubePartition S hscale Y hsource).fineIndices =
      S.activeFine := by
  rfl

@[simp] theorem sourceMassCoarseTubePartition_coarseIndices
    (S : StickyScaleCover fine rho) (hscale : delta ≤ rho)
    (Y : Shading fine.bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass ≠
        0) :
    (sourceMassCoarseTubePartition S hscale Y hsource).coarseIndices =
      S.activeCoarse := by
  rfl

/-- A literal Sticky cover with nonzero active source mass produces the full
same-data frozen dyadic assembly.  The loss is polylogarithmic in the actual
fine and coarse index types, and all masses, densities, and average
multiplicities below are those of the actual surviving shadings. -/
theorem exists_frozenComparableAssembly_of_stickyScaleCover
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
      (Assembly.sourceActiveFineShading
          (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
          Y).shadingMass ≤
        (frozenComparableLoss iota (Fin S.coarseCard) : ENNReal) *
          (Assembly.actualRefinementShading A).shadingMass ∧
      (Assembly.sourceActiveFineShading
          (sourceMassCoarseTubePartition S hscale Y hsource).asConvexFactorization
          Y).shadingDensity /
          (frozenComparableLoss iota (Fin S.coarseCard) : ENNReal) ≤
        (Assembly.actualRefinementShading A).shadingDensity ∧
      ∃ k ∈ S.activeCoarse,
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
  simpa [sourceMassCoarseTubePartition] using
    (exists_frozenComparableAssembly_of_coarseTubePartition
      (sourceMassCoarseTubePartition S hscale Y hsource) Y r hr
      (by simpa using hsource))

#print axioms activeCoarse_nonempty_of_restricted_shadingMass_ne_zero
#print axioms sourceMassCoarseTubePartition
#print axioms exists_frozenComparableAssembly_of_stickyScaleCover

end

end Family8StickyScaleCoverFrozenComparableAdapterV2
