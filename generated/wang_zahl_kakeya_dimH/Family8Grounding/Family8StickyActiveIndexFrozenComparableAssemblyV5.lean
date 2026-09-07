import Family8Grounding.Family8StickyScaleCoverActiveFineRestrictionV2
import Family8Grounding.Family8StickyScaleCoverFrozenComparableAdapterV2
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Mathlib.Tactic

/-!
# Frozen comparable assembly on the genuine active index types, V5

The active-fine and active-coarse sets are first reindexed as literal
universes.  Thus the two comparable-level logarithms see only actual active
indices, never inactive dummy entries of the ambient cover.  The source
active average and the same actual outer/fibre product are retained.

V1 used Boolean inequality notation in dependent proof arguments.  V2
exposed an active-fine family reducibility mismatch; V3 and V4 exposed the
analogous dependent coarse-cardinality rewrite.  No failed draft is imported;
V5 compares the two numerical losses only after unfolding their finite-cardinal
formula.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyActiveIndexFrozenComparableAssemblyV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8SourceActiveFineActualAverageIdentityV2
open Family8NormalizedCrossingSourceTauShadingV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

local instance family8ActiveIndexFrozenPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The literal active shading, stated on the precise restricted-family
definition consumed by `activeFineRestrictedScaleCover`. -/
def activeFineRestrictedShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    Shading (activeFineRestrictedFamily S).bodyFamily where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

@[simp]
theorem activeFineRestrictedShading_carrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (i : {i // i ∈ S.activeFine}) :
    (activeFineRestrictedShading S Y).carrier i = Y.carrier i.1 :=
  rfl

theorem activeFineRestrictedShading_shadingMass
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    (activeFineRestrictedShading S Y).shadingMass =
      (activeFineShading S Y).shadingMass :=
  rfl

theorem activeFineRestrictedShading_shadedUnion
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    (activeFineRestrictedShading S Y).shadedUnion =
      (activeFineShading S Y).shadedUnion :=
  rfl

theorem activeFineRestrictedShading_averageMultiplicity
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    (activeFineRestrictedShading S Y).averageMultiplicity =
      (activeFineShading S Y).averageMultiplicity :=
  rfl

theorem restrictTo_univ_shadingMass
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    {F : ConvexFamily alpha} (Y : Shading F) :
    (IndexedShadingRefinement.restrictTo Y
      (Finset.univ : Finset alpha)).shading.shadingMass = Y.shadingMass := by
  rw [shadingMass_restrictTo_eq_sum, Shading.shadingMass]

theorem restrictTo_univ_shadedUnion
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    {F : ConvexFamily alpha} (Y : Shading F) :
    (IndexedShadingRefinement.restrictTo Y
      (Finset.univ : Finset alpha)).shading.shadedUnion = Y.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    rw [IndexedShadingRefinement.restrictTo_carrier,
      if_pos (Finset.mem_univ i)] at hxi
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [IndexedShadingRefinement.restrictTo_carrier,
      if_pos (Finset.mem_univ i)]
    exact hxi

theorem restrictTo_univ_averageMultiplicity
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    {F : ConvexFamily alpha} (Y : Shading F) :
    (IndexedShadingRefinement.restrictTo Y
      (Finset.univ : Finset alpha)).shading.averageMultiplicity =
        Y.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [restrictTo_univ_shadingMass, restrictTo_univ_shadedUnion]

theorem activeFineRestrictedSourceMass_ne_zero
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0) :
    (IndexedShadingRefinement.restrictTo
      (activeFineRestrictedShading S Y)
      (activeFineRestrictedScaleCover S).activeFine).shading.shadingMass ≠
        0 := by
  rw [activeFineRestrictedScaleCover_activeFine,
    restrictTo_univ_shadingMass,
    activeFineRestrictedShading_shadingMass,
    activeFineShading_shadingMass_eq_restrictTo]
  exact hsource

theorem activeCoarse_card_le_activeFine_card
    (S : StickyScaleCover fine rho) :
    S.activeCoarse.card ≤ S.activeFine.card := by
  let parent : {i // i ∈ S.activeFine} → {k // k ∈ S.activeCoarse} :=
    fun i => ⟨S.parent i.1, S.parent_mem i.1 i.2⟩
  have hsurj : Function.Surjective parent := by
    intro k
    obtain ⟨i, hi, hparent⟩ := S.parent_surjective k.1 k.2
    refine ⟨⟨i, hi⟩, ?_⟩
    apply Subtype.ext
    exact hparent
  have hcard := Fintype.card_le_of_surjective parent hsurj
  simpa only [Fintype.card_coe] using hcard

theorem exists_activeIndex_frozenComparableAssembly
    (S : StickyScaleCover fine rho) (hscale : delta ≤ rho)
    (Y : Shading fine.bodyFamily) (r : Real) (hr : 0 < r)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y
        S.activeFine).shading.shadingMass ≠ 0) :
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition
          (activeFineRestrictedScaleCover S) hscale
          (activeFineRestrictedShading S Y)
          (activeFineRestrictedSourceMass_ne_zero S Y hsource)).asConvexFactorization
        (activeFineRestrictedShading S Y) r,
      A.loss = frozenComparableLoss {i // i ∈ S.activeFine}
        (Fin S.activeCoarse.card) ∧
      (activeFineShading S Y).averageMultiplicity ≤
        (frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin S.activeCoarse.card) : ENNReal) *
          (actualRefinementShading A).averageMultiplicity ∧
      ∃ k : Fin S.activeCoarse.card,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  obtain ⟨A, hloss, _hfiberLabel, _houterLabel, _hmass, _hdensity,
      k, _hk, hfiber, _hfiberLower, _hfiberUpper, _houterLower,
      _houterUpper, hproduct⟩ :=
    exists_frozenComparableAssembly_of_stickyScaleCover
      (activeFineRestrictedScaleCover S) hscale
      (activeFineRestrictedShading S Y) r hr
      (activeFineRestrictedSourceMass_ne_zero S Y hsource)
  refine ⟨A, hloss, ?_, k, hfiber, hproduct⟩
  have havg :=
    restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement A
  have hfineIndices :
      (sourceMassCoarseTubePartition
        (activeFineRestrictedScaleCover S) hscale
        (activeFineRestrictedShading S Y)
        (activeFineRestrictedSourceMass_ne_zero S Y hsource)).fineIndices =
          Finset.univ := by
    rw [sourceMassCoarseTubePartition_fineIndices,
      activeFineRestrictedScaleCover_activeFine]
  change
    (IndexedShadingRefinement.restrictTo
      (activeFineRestrictedShading S Y)
      (sourceMassCoarseTubePartition
        (activeFineRestrictedScaleCover S) hscale
        (activeFineRestrictedShading S Y)
        (activeFineRestrictedSourceMass_ne_zero S Y hsource)).fineIndices).shading.averageMultiplicity ≤
      (A.loss : ENNReal) * (actualRefinementShading A).averageMultiplicity
      at havg
  rw [hfineIndices, restrictTo_univ_averageMultiplicity,
    activeFineRestrictedShading_averageMultiplicity] at havg
  have hcoarseCard :
      (activeFineRestrictedScaleCover S).coarseCard =
        S.activeCoarse.card := by
    rfl
  have hlossValue :
      frozenComparableLoss {i // i ∈ S.activeFine}
          (Fin (activeFineRestrictedScaleCover S).coarseCard) =
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

#print axioms activeFineRestrictedShading_averageMultiplicity
#print axioms restrictTo_univ_averageMultiplicity
#print axioms activeFineRestrictedSourceMass_ne_zero
#print axioms activeCoarse_card_le_activeFine_card
#print axioms exists_activeIndex_frozenComparableAssembly

end

end Family8StickyActiveIndexFrozenComparableAssemblyV5
