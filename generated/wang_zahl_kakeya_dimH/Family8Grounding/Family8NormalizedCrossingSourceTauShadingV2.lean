import Family8Grounding.Family8NormalizedCrossingFrozenComparableAdapterV3
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import Mathlib.Tactic

/-!
# Actual source-to-tau shading for a normalized crossing

The coherent source-to-`tau` cover naturally produces a parent-aggregated
shading on the active coarse subtype.  A later `tau`-to-`rho` interval cover,
however, is parameterized by the full `tau` coarse family.  This file closes
that literal data seam by extending the active-subtype shading by the empty
set off the active indices.  Restriction back to the active indices preserves
shading mass exactly.

Nonzero source mass on the actual source-to-`tau` active restriction implies
nonzero parent-aggregated mass by the already proved finite-fibre inequality.
Consequently the zero extension automatically supplies the nonzero source
premise of the frozen normalized-crossing adapter.  No retention estimate or
target conclusion is assumed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8NormalizedCrossingSourceTauShadingV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingFrozenComparableAdapterV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance family8SourceTauShadingPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {delta rho : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- Extend a shading of the genuine active coarse subtype to the full coarse
family by putting the empty shading on every inactive index. -/
def extendActiveCoarseShading (S : StickyScaleCover fine rho)
    (Z : Shading S.activeCoarseFamily) :
    Shading S.coarse.bodyFamily where
  carrier := fun k =>
    if hk : k ∈ S.activeCoarse then Z.carrier ⟨k, hk⟩ else ∅
  measurable_carrier := by
    intro k
    by_cases hk : k ∈ S.activeCoarse
    · simpa only [dif_pos hk] using Z.measurable_carrier ⟨k, hk⟩
    · simp only [dif_neg hk]
      exact MeasurableSet.empty
  carrier_subset := by
    intro k
    by_cases hk : k ∈ S.activeCoarse
    · simp only [dif_pos hk]
      simpa [FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.activeCoarseFamily,
        UniformTubeFamily.bodyFamily] using Z.carrier_subset ⟨k, hk⟩
    · simp only [dif_neg hk, empty_subset]

@[simp] theorem extendActiveCoarseShading_carrier_of_mem
    (S : StickyScaleCover fine rho) (Z : Shading S.activeCoarseFamily)
    (k : Fin S.coarseCard) (hk : k ∈ S.activeCoarse) :
    (extendActiveCoarseShading S Z).carrier k = Z.carrier ⟨k, hk⟩ := by
  simp [extendActiveCoarseShading, hk]

@[simp] theorem extendActiveCoarseShading_carrier_of_not_mem
    (S : StickyScaleCover fine rho) (Z : Shading S.activeCoarseFamily)
    (k : Fin S.coarseCard) (hk : k ∉ S.activeCoarse) :
    (extendActiveCoarseShading S Z).carrier k = ∅ := by
  simp [extendActiveCoarseShading, hk]

/-- The active-subtype shading mass is exactly the mass of the corresponding
full-family restriction. -/
theorem activeFineShading_shadingMass_eq_restrictTo
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily) :
    (activeFineShading S Y).shadingMass =
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass := by
  classical
  rw [shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass activeFineShading
  rw [← Finset.attach_eq_univ]
  exact Finset.sum_attach S.activeFine
    (fun i => volume (Y.carrier i))

/-- Nonzero mass on the actual active fine restriction survives literal
parent aggregation.  The proof uses the existing exact finite fibre-card
loss, rather than a positivity callback. -/
theorem parentAggregatedShading_shadingMass_ne_zero_of_restrictTo
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (hsource :
      (IndexedShadingRefinement.restrictTo Y S.activeFine).shading.shadingMass ≠
        0) :
    (parentAggregatedShading S Y).shadingMass ≠ 0 := by
  have hactive : (activeFineShading S Y).shadingMass ≠ 0 := by
    rwa [activeFineShading_shadingMass_eq_restrictTo S Y]
  have hbound :=
    activeFineShading_shadingMass_le_nsmul_parent_of_fiberCard_le
      S Y (Fintype.card {i // i ∈ S.activeFine})
      (fun k => Finset.card_le_univ
        ((activeIndexFactorization S).fiber k))
  intro hparent
  apply hactive
  apply le_antisymm
  · calc
      (activeFineShading S Y).shadingMass ≤
          (Fintype.card {i // i ∈ S.activeFine}) •
            (parentAggregatedShading S Y).shadingMass := hbound
      _ = 0 := by simp [hparent]
  · exact bot_le

/-- Extending an active-coarse shading by zero and then restricting to the
same literal active set preserves total shading mass exactly. -/
theorem restrictTo_extendActiveCoarseShading_shadingMass
    (S : StickyScaleCover fine rho) (Z : Shading S.activeCoarseFamily) :
    (IndexedShadingRefinement.restrictTo
      (extendActiveCoarseShading S Z) S.activeCoarse).shading.shadingMass =
      Z.shadingMass := by
  classical
  rw [shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass
  rw [← Finset.attach_eq_univ]
  rw [← Finset.sum_attach S.activeCoarse
    (fun k => volume ((extendActiveCoarseShading S Z).carrier k))]
  apply Finset.sum_congr rfl
  intro k hk
  simp [extendActiveCoarseShading]

variable {sourceDelta : NNReal} {sourceIndex : Type}
  [Fintype sourceIndex] [DecidableEq sourceIndex]
  {depth : Nat}

/-- The exact source-to-`tau_m` cover underlying the lower family named in
the normalized-crossing adapter. -/
def sourceTauCover
    (D : ActualTubeDatum sourceDelta sourceIndex)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth) (m : Fin depth) :
    StickyScaleCover D.family (S.tau m) :=
  C.base.cover (S.tau m) (S.delta_le_tau m)
    (CoherentStickyMultiscaleCover.tau_le_one S m)

/-- The canonical full-family shading at `tau_m`: aggregate actual source
pieces inside their literal `tau_m` parent and extend by zero off the active
parent set. -/
def sourceTauFullShading
    (D : ActualTubeDatum sourceDelta sourceIndex)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth) (m : Fin depth) :
    Shading (bufferedLowerFamily D C S m).bodyFamily :=
  extendActiveCoarseShading (sourceTauCover D C S m)
    (parentAggregatedShading (sourceTauCover D C S m) D.shading)

/-- The active fine indices of the literal buffered interval are exactly the
active parent indices of the source-to-`tau_m` cover. -/
@[simp] theorem bufferedIntervalCover_activeFine
    (D : ActualTubeDatum sourceDelta sourceIndex) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :
    (bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered).activeFine =
      (sourceTauCover D C S m).activeCoarse := by
  rfl

/-- Exact mass identification for the source-produced full `tau_m` shading
on the interval cover's literal active fine set. -/
theorem sourceTauFullShading_restrictedMass_eq_parentAggregated
    (D : ActualTubeDatum sourceDelta sourceIndex) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :
    (IndexedShadingRefinement.restrictTo
      (sourceTauFullShading D C S m)
      (bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered).activeFine).shading.shadingMass =
        (parentAggregatedShading (sourceTauCover D C S m) D.shading).shadingMass := by
  change
    (IndexedShadingRefinement.restrictTo
      (extendActiveCoarseShading (sourceTauCover D C S m)
        (parentAggregatedShading (sourceTauCover D C S m) D.shading))
      (sourceTauCover D C S m).activeCoarse).shading.shadingMass =
        (parentAggregatedShading (sourceTauCover D C S m) D.shading).shadingMass
  exact restrictTo_extendActiveCoarseShading_shadingMass
    (sourceTauCover D C S m)
    (parentAggregatedShading (sourceTauCover D C S m) D.shading)

/-- A nonzero actual source-to-`tau_m` active mass automatically produces the
nonzero full-lower-family premise consumed by the normalized-crossing frozen
assembly. -/
theorem sourceTauFullShading_restrictedMass_ne_zero
    (D : ActualTubeDatum sourceDelta sourceIndex) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence sourceDelta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho)
    (hsourceTau :
      (IndexedShadingRefinement.restrictTo D.shading
        (sourceTauCover D C S m).activeFine).shading.shadingMass ≠ 0) :
    (IndexedShadingRefinement.restrictTo
      (sourceTauFullShading D C S m)
      (bufferedIntervalCover D hD C S epsilon hepsilon m rho hbuffered).activeFine).shading.shadingMass ≠
        0 := by
  rw [sourceTauFullShading_restrictedMass_eq_parentAggregated]
  exact parentAggregatedShading_shadingMass_ne_zero_of_restrictTo
    (sourceTauCover D C S m) D.shading hsourceTau

#print axioms extendActiveCoarseShading
#print axioms activeFineShading_shadingMass_eq_restrictTo
#print axioms parentAggregatedShading_shadingMass_ne_zero_of_restrictTo
#print axioms restrictTo_extendActiveCoarseShading_shadingMass
#print axioms sourceTauFullShading
#print axioms sourceTauFullShading_restrictedMass_eq_parentAggregated
#print axioms sourceTauFullShading_restrictedMass_ne_zero

end

end Family8NormalizedCrossingSourceTauShadingV2
