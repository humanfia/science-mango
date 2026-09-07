import Family8Grounding.Family8StickyActiveKatzTaoBoundedFrozenAssemblyScaleV2
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveKatzTaoBoundedFrozenAssemblySourceAverageV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8StickyActiveKatzTaoBoundedFrozenAssemblyScaleV2
open Family8SourceActiveFineActualAverageIdentityV2

noncomputable section

/-!
# Same-data source-average product for the bounded frozen producer

The actual bounded assembly, its positive final fibre, the outer/fibre
product, and source-average retention all use the same literal `P/A/k`.
V1 and V2 are failed namespace/definitional-rewrite drafts and are not
imported.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem exists_activeKatzTaoBounded_frozenComparable_sourceAverageProduct
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hscale : delta ≤ rho)
    (hrhoOne : rho ≤ 1)
    {K : ENNReal} (hKfinite : K ≠ ∞)
    (hKT : IsKatzTao K D.family.bodyFamily)
    (r : Real) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo D.shading
        S.activeFine).shading.shadingMass ≠ 0) :
    let U := activeFineRestrictedScaleCover S
    let Y := activeFineRestrictedShading S D.shading
    let hsource' :
        (IndexedShadingRefinement.restrictTo Y
          U.activeFine).shading.shadingMass ≠ 0 :=
      activeFineRestrictedSourceMass_ne_zero S D.shading hsource
    let M := katzTaoDoubledFiberNatCap delta rho K
    let hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card ≤ M :=
      activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
        S hdeltaPos hdeltaHalf hrhoOne hKfinite hKT
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource'
    let P := boundedFiberCoarseTubePartition U hscale hcoarse M hM
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        P.asConvexFactorization Y r,
      A.loss = frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin U.coarseCard) ∧
      ∃ k ∈ P.coarseIndices,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) ∧
        (activeFineShading S D.shading).averageMultiplicity ≤
          (4 * (A.loss : ENNReal)) *
            (A.frozenCoarse.averageMultiplicity *
              (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  let U := activeFineRestrictedScaleCover S
  let Y := activeFineRestrictedShading S D.shading
  let hsource' :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero S D.shading hsource
  let M := katzTaoDoubledFiberNatCap delta rho K
  let hM : ∀ k, k ∈ U.activeCoarse → (U.fiber k).card ≤ M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      S hdeltaPos hdeltaHalf hrhoOne hKfinite hKT
  let hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource'
  let P := boundedFiberCoarseTubePartition U hscale hcoarse M hM
  obtain ⟨A, hAloss, _hmass, _hdensity, k, hk, hkpositive, hproduct⟩ :=
    exists_activeKatzTaoBounded_frozenComparableAssembly_of_scale
      D S hdeltaPos hdeltaHalf hscale hrhoOne hKfinite hKT r hr hsource
  have havg := restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement A
  have hfineIndices : P.fineIndices = Finset.univ := by
    change U.activeFine = Finset.univ
    exact activeFineRestrictedScaleCover_activeFine S
  have hsourceAverage :
      (activeFineShading S D.shading).averageMultiplicity ≤
        (A.loss : ENNReal) *
          (actualRefinementShading A).averageMultiplicity := by
    change
      (IndexedShadingRefinement.restrictTo Y
        P.fineIndices).shading.averageMultiplicity ≤
          (A.loss : ENNReal) *
            (actualRefinementShading A).averageMultiplicity at havg
    rw [hfineIndices, restrictTo_univ_averageMultiplicity,
      activeFineRestrictedShading_averageMultiplicity] at havg
    exact havg
  have hsourceProduct :
      (activeFineShading S D.shading).averageMultiplicity ≤
        (4 * (A.loss : ENNReal)) *
          (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
    calc
      (activeFineShading S D.shading).averageMultiplicity ≤
          (A.loss : ENNReal) *
            (actualRefinementShading A).averageMultiplicity := hsourceAverage
      _ ≤ (A.loss : ENNReal) *
          (4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity)) :=
        mul_le_mul' le_rfl hproduct
      _ = (4 * (A.loss : ENNReal)) *
          (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
        ac_rfl
  exact ⟨A, hAloss, k, hk, hkpositive, hproduct, hsourceProduct⟩

#print axioms
  exists_activeKatzTaoBounded_frozenComparable_sourceAverageProduct

end
end Family8StickyActiveKatzTaoBoundedFrozenAssemblySourceAverageV3
