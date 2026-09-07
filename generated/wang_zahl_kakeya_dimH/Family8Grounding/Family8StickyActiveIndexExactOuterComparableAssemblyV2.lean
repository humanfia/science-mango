import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickyScaleCoverExactOuterComparableAdapterV1
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2

/-!
# Exact-outer comparable assembly on genuine active index types, V2

The restricted cover, shading, source-mass proof, and factorization are
refolded as local data before the dependent assembly statement.  This keeps
the exact induced-outer identity literal while avoiding repeated expansion
of proof-dependent source-mass partitions.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyActiveIndexExactOuterComparableAssemblyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8SourceActiveFineActualAverageIdentityV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverExactOuterComparableAdapterV1
open Family8StickyScaleCoverFrozenComparableAdapterV2

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Active reindexing preserves the exact induced outer shading together
with the actual source-average and same-product conclusions. -/
theorem exists_activeIndex_exactOuterComparableAssembly
    (S : StickyScaleCover fine rho) (hscale : delta ≤ rho)
    (Y : Shading fine.bodyFamily) (r : Real) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0) :
    let T := activeFineRestrictedScaleCover S
    let YR := activeFineRestrictedShading S Y
    let hsourceR := activeFineRestrictedSourceMass_ne_zero S Y hsource
    let P := (sourceMassCoarseTubePartition T hscale YR hsourceR).asConvexFactorization
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly P YR r,
      A.loss = frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) ∧
      (activeFineShading S Y).averageMultiplicity ≤
        (frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin S.activeCoarse.card) : ENNReal) *
          (actualRefinementShading A).averageMultiplicity ∧
      A.frozenCoarse = P.inducedShading A.refinement.shading ∧
      ∃ k : Fin S.activeCoarse.card,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  let T := activeFineRestrictedScaleCover S
  let YR := activeFineRestrictedShading S Y
  let hsourceR := activeFineRestrictedSourceMass_ne_zero S Y hsource
  let P := (sourceMassCoarseTubePartition T hscale YR hsourceR).asConvexFactorization
  change ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly P YR r,
    A.loss = frozenComparableLoss {i // i ∈ S.activeFine}
      (Fin S.activeCoarse.card) ∧
    (activeFineShading S Y).averageMultiplicity ≤
      (frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) : ENNReal) *
        (actualRefinementShading A).averageMultiplicity ∧
    A.frozenCoarse = P.inducedShading A.refinement.shading ∧
    ∃ k : Fin S.activeCoarse.card,
      0 < volume (finalFiberShading A k).shadedUnion ∧
      (actualRefinementShading A).averageMultiplicity ≤
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A k).averageMultiplicity)
  obtain ⟨A, hloss, _hfiberLabel, _houterLabel, hExactOuter,
      _hmass, _hdensity, k, _hk, hfiber, _hfiberLower, _hfiberUpper,
      _houterLower, _houterUpper, hproduct⟩ :=
    exists_exactOuter_frozenComparableAssembly_of_stickyScaleCover
      T hscale YR r hr hsourceR
  refine ⟨A, hloss, ?_, hExactOuter, k, hfiber, hproduct⟩
  have havg :=
    restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement A
  have hfineIndices :
      (sourceMassCoarseTubePartition T hscale YR hsourceR).fineIndices =
        Finset.univ := by
    rw [sourceMassCoarseTubePartition_fineIndices,
      activeFineRestrictedScaleCover_activeFine]
  change
    (IndexedShadingRefinement.restrictTo YR
      (sourceMassCoarseTubePartition
        T hscale YR hsourceR).fineIndices).shading.averageMultiplicity ≤
      (A.loss : ENNReal) * (actualRefinementShading A).averageMultiplicity
      at havg
  rw [hfineIndices, restrictTo_univ_averageMultiplicity,
    activeFineRestrictedShading_averageMultiplicity] at havg
  have hcoarseCard : T.coarseCard = S.activeCoarse.card := by
    rfl
  have hlossValue :
      frozenComparableLoss {i // i ∈ S.activeFine} (Fin T.coarseCard) =
        frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin S.activeCoarse.card) := by
    simp only [frozenComparableLoss, Fintype.card_fin]
    rw [hcoarseCard]
  calc
    (activeFineShading S Y).averageMultiplicity ≤
        (A.loss : ENNReal) *
          (actualRefinementShading A).averageMultiplicity := havg
    _ = (frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin S.activeCoarse.card) : ENNReal) *
          (actualRefinementShading A).averageMultiplicity := by
      rw [hloss, hlossValue]

#print axioms exists_activeIndex_exactOuterComparableAssembly

end
end Family8StickyActiveIndexExactOuterComparableAssemblyV2
