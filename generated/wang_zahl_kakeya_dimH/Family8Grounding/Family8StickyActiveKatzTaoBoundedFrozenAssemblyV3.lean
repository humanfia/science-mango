import Family8Grounding.Family8StickyKatzTaoBoundedFiberPartitionV4
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8FrozenCoarseSameDataMassTransportV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyActiveKatzTaoBoundedFrozenAssemblyV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open FamilyStickyAtEveryScaleCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8FrozenComparableActualAverageMassDensityV1
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyKatzTaoBoundedFiberPartitionV4
open Family8FrozenCoarseSameDataMassTransportV3

noncomputable section

/-!
# Frozen assembly with the native Katz--Tao fibre cap

This producer uses the exact incidence cap as the branching loss of the
literal active-index parent partition.  Thus the same frozen assembly that
carries the actual outer/fibre averages also carries a source-to-frozen mass
comparison with no global active-cardinality fallback.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem exists_activeKatzTaoBounded_frozenComparableAssembly
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hscale : delta <= rho)
    (hrhoOne : rho <= 1)
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
    let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
      activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
        S hD.delta_pos hD.delta_le_half hrhoOne hKfinite hKT
    let hcoarse : U.activeCoarse.Nonempty :=
      activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource'
    let P := boundedFiberCoarseTubePartition U hscale hcoarse M hM
    exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        P.asConvexFactorization Y r,
      A.loss = frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin U.coarseCard) /\
      (Assembly.sourceActiveFineShading P.asConvexFactorization Y).shadingMass <=
        ((A.loss : ENNReal) * (M : ENNReal)) *
          A.frozenCoarse.shadingMass /\
      (Assembly.sourceActiveFineShading P.asConvexFactorization Y).shadingDensity *
          familyVolume (Assembly.sourceActiveFineFamily P.asConvexFactorization) <=
        ((A.loss : ENNReal) * (M : ENNReal)) *
          (A.frozenCoarse.shadingDensity *
            familyVolume U.coarse.bodyFamily) /\
      ∃ k ∈ P.coarseIndices,
        0 < volume (Assembly.finalFiberShading A k).shadedUnion /\
        (Assembly.actualRefinementShading A).averageMultiplicity <=
          4 * (A.frozenCoarse.averageMultiplicity *
            (Assembly.finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  let U := activeFineRestrictedScaleCover S
  let Y := activeFineRestrictedShading S D.shading
  let hsource' :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 :=
    activeFineRestrictedSourceMass_ne_zero S D.shading hsource
  let M := katzTaoDoubledFiberNatCap delta rho K
  let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= M :=
    activeFineRestrictedScaleCover_fiber_card_le_katzTaoCap
      S hD.delta_pos hD.delta_le_half hrhoOne hKfinite hKT
  let hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource'
  let P := boundedFiberCoarseTubePartition U hscale hcoarse M hM
  have hsourceP :
      (IndexedShadingRefinement.restrictTo Y
        P.fineIndices).shading.shadingMass ≠ 0 := by
    simpa only [P, boundedFiberCoarseTubePartition,
      CoarseTubePartition.fineIndices,
      FamilyStickyScaleCoverAdjacentStepBridgeV2.coverIndexFactorization] using
        hsource'
  obtain ⟨A, hloss, _hfiberLabel, _houterLabel, _hmass, _hdensity,
      k, hk, hpositive, _hfiberLower, _hfiberUpper,
      _houterLower, _houterUpper, hproduct⟩ :=
    Family8CoarseTubePartitionFrozenComparableAdapterV1.exists_frozenComparableAssembly_of_coarseTubePartition
      P Y r hr hsourceP
  refine ⟨A, ?_, ?_, ?_, k, hk, hpositive, hproduct⟩
  · simpa only [U, Y, P] using hloss
  · have hmass :=
      Family8FrozenCoarseSameDataMassTransportV3.Assembly.sourceActiveFineShading_mass_le_loss_mul_branching_mul_frozenCoarse
        (P := P) A
    simpa only [P, boundedFiberCoarseTubePartition_branchingLoss,
      boundedFiberCoarseTubePartition_branching, Nat.mul_one] using hmass
  · have hdensity :=
      Family8FrozenCoarseSameDataMassTransportV3.Assembly.sourceDensity_mul_sourceVolume_le_loss_mul_branching_mul_frozenDensityVolume
        (P := P) A
    simpa only [P, boundedFiberCoarseTubePartition_branchingLoss,
      boundedFiberCoarseTubePartition_branching, Nat.mul_one] using hdensity

#print axioms exists_activeKatzTaoBounded_frozenComparableAssembly

end
end Family8StickyActiveKatzTaoBoundedFrozenAssemblyV3
