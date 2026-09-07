import Family8Grounding.Family8NormalizedCrossingSourceTauFrozenAssemblyV1
import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Mathlib.Tactic

/-!
# Actual source-to-tau average retained by the normalized frozen assembly, V2

The canonical source shading at `tau` is obtained by extending the genuine
active-parent aggregation by zero.  Restricting that extension back to the
same active parents preserves its literal union and average multiplicity.
The normalized-crossing frozen producer therefore retains the actual
parent-aggregated source average on the same final refinement that carries
the outer/fibre product.

V1 is a failed namespace/rewrite draft and is not imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedCrossingSourceTauActualAverageV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8ComparableMultiplicityBucketsV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8NormalizedCrossingFrozenComparableAdapterV3
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedCrossingSourceTauFrozenAssemblyV1
open Family8SourceActiveFineActualAverageIdentityV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

local instance family8SourceTauAveragePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Restricting the zero extension of an active-parent shading back to its
literal active set preserves the shaded union exactly. -/
theorem restrictTo_extendActiveCoarseShading_shadedUnion
    (S : StickyScaleCover fine rho) (Z : Shading S.activeCoarseFamily) :
    (IndexedShadingRefinement.restrictTo
      (extendActiveCoarseShading S Z) S.activeCoarse).shading.shadedUnion =
        Z.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    rw [IndexedShadingRefinement.restrictTo_carrier] at hxk
    by_cases hk : k ∈ S.activeCoarse
    · rw [if_pos hk, extendActiveCoarseShading_carrier_of_mem S Z k hk] at hxk
      exact Set.mem_iUnion.mpr ⟨⟨k, hk⟩, hxk⟩
    · rw [if_neg hk] at hxk
      exact hxk.elim
  · intro hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨k.1, ?_⟩
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos k.2,
      extendActiveCoarseShading_carrier_of_mem S Z k.1 k.2]
    exact hxk

/-- The corresponding average multiplicities agree, including at zero
volume. -/
theorem restrictTo_extendActiveCoarseShading_averageMultiplicity
    (S : StickyScaleCover fine rho) (Z : Shading S.activeCoarseFamily) :
    (IndexedShadingRefinement.restrictTo
      (extendActiveCoarseShading S Z) S.activeCoarse).shading.averageMultiplicity =
        Z.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [restrictTo_extendActiveCoarseShading_shadingMass,
    restrictTo_extendActiveCoarseShading_shadedUnion]

variable {sourceDelta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat}

/-- The full zero-extended `tau_m` shading restricted to the buffered
interval's actual fine set has the literal parent-aggregated average. -/
theorem sourceTauFullShading_restrictedAverage_eq_parentAggregated
    (D : ActualTubeDatum sourceDelta sourceIndex) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :
    (IndexedShadingRefinement.restrictTo
      (sourceTauFullShading D C S m)
      (bufferedIntervalCover D hD C S epsilon hepsilon m rho
        hbuffered).activeFine).shading.averageMultiplicity =
      (parentAggregatedShading (sourceTauCover D C S m)
        D.shading).averageMultiplicity := by
  change
    (IndexedShadingRefinement.restrictTo
      (extendActiveCoarseShading (sourceTauCover D C S m)
        (parentAggregatedShading (sourceTauCover D C S m) D.shading))
      (sourceTauCover D C S m).activeCoarse).shading.averageMultiplicity = _
  exact restrictTo_extendActiveCoarseShading_averageMultiplicity
    (sourceTauCover D C S m)
    (parentAggregatedShading (sourceTauCover D C S m) D.shading)

/-- Callback-free normalized-crossing producer with the actual source
parent-average retained on the same final refinement as the frozen product. -/
theorem exists_frozenComparableAssembly_with_sourceTau_actualAverage
    (D : ActualTubeDatum sourceDelta sourceIndex) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho)
    (r : Real) (hr : 0 < r)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D C S m).activeFine).shading.shadingMass ≠ 0) :
    let Y := sourceTauFullShading D C S m
    let U := bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered
    let hsource :
        (IndexedShadingRefinement.restrictTo Y U.activeFine).shading.shadingMass ≠
          0 :=
      sourceTauFullShading_restrictedMass_ne_zero
        D hD C S epsilon hepsilon m rho hbuffered hsourceTau
    ∃ A : Family8FrozenNeighborhoodAssemblyV1.Assembly
        (sourceMassCoarseTubePartition U
          (actualDatum_tau_le_of_isBuffered
            D hD S hepsilon m rho hbuffered) Y hsource).asConvexFactorization
          Y r,
      A.loss = frozenComparableLoss (bufferedLowerIndex D C S m)
        (Fin U.coarseCard) ∧
      (parentAggregatedShading (sourceTauCover D C S m)
          D.shading).averageMultiplicity ≤
        (frozenComparableLoss (bufferedLowerIndex D C S m)
          (Fin U.coarseCard) : ENNReal) *
          (actualRefinementShading A).averageMultiplicity ∧
      ∃ k ∈ U.activeCoarse,
        0 < volume (finalFiberShading A k).shadedUnion ∧
        (actualRefinementShading A).averageMultiplicity ≤
          4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A k).averageMultiplicity) := by
  dsimp only
  obtain ⟨A, hloss, _hfiberLabel, _houterLabel, _hmass, _hdensity,
      k, hk, hfiber, _hfiberLower, _hfiberUpper, _houterLower,
      _houterUpper, hproduct⟩ :=
    exists_frozenComparableAssembly_of_sourceTauActiveMass
      D hD C S epsilon hepsilon m rho hbuffered r hr hsourceTau
  refine ⟨A, hloss, ?_, k, hk, hfiber, hproduct⟩
  have hretained :=
    restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement A
  change
    (IndexedShadingRefinement.restrictTo
      (sourceTauFullShading D C S m)
      (sourceMassCoarseTubePartition
        (bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered)
        (actualDatum_tau_le_of_isBuffered
          D hD S hepsilon m rho hbuffered)
        (sourceTauFullShading D C S m)
        (sourceTauFullShading_restrictedMass_ne_zero
          D hD C S epsilon hepsilon m rho hbuffered
            hsourceTau)).fineIndices).shading.averageMultiplicity ≤
      (A.loss : ENNReal) * (actualRefinementShading A).averageMultiplicity
      at hretained
  rw [sourceMassCoarseTubePartition_fineIndices] at hretained
  rw [sourceTauFullShading_restrictedAverage_eq_parentAggregated
    D hD C S epsilon hepsilon m rho hbuffered] at hretained
  simpa only [hloss] using hretained

#print axioms restrictTo_extendActiveCoarseShading_shadedUnion
#print axioms restrictTo_extendActiveCoarseShading_averageMultiplicity
#print axioms sourceTauFullShading_restrictedAverage_eq_parentAggregated
#print axioms exists_frozenComparableAssembly_with_sourceTau_actualAverage

end

end Family8NormalizedCrossingSourceTauActualAverageV2
