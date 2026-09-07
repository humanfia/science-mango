import Family8Grounding.Family8PlankActiveSelectedOwnerRepresentativeDatumV1
import Family8Grounding.Family8PlankRetainedOwnerThickenedMassTransportV1
import FamilyStickyGrounding.FamilyStickyConvexClosedThickeningBoxGrowthV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankActiveSelectedOwnerFlatPrismCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.ConvexFactoring.CubeWeightUniformization
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6PlankKatzTaoFrostmanActualAdaptersV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerThickenedInducedShadingV2
open Family8PlankRetainedOwnerThickenedMassTransportV1
open Family8PlankRetainedOwnerCellRestrictedCanonicalSlabV1
open Family8PlankRetainedOwnerActiveCellCommonBallContainerV1
open Family8PlankRetainedOwnerActiveCertifiedOwnerIncidenceV1
open Family8PlankActiveSelectedOwnerRepresentativeDatumV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# A literal flat-prism volume/count reserve for the active selected owners

The previous modules put every selected owner plank in the same closed
thickening of a certified slab.  Here that set is packaged as an actual
compact convex body.  The certified outer FrameBox gives its volume directly.
Applying the genuine maximal concentration of the original plank family to
this body gives a cross-multiplied cardinal bound for the deduplicated owner
row.  No target count reserve is supplied as a premise.
-/

/-- Closed thickening of an arbitrary convex body, packaged as a convex body. -/
def closedThickeningConvexBody (K : ConvexBody Space) (r : NNReal) :
    ConvexBody Space where
  carrier := Metric.cthickening (r : Real) (K : Set Space)
  convex' := K.convex.cthickening _
  isCompact' := K.isCompact.cthickening
  nonempty' := K.nonempty.mono (Metric.self_subset_cthickening _)

@[simp] theorem coe_closedThickeningConvexBody
    (K : ConvexBody Space) (r : NNReal) :
    (closedThickeningConvexBody K r : Set Space) =
      Metric.cthickening (r : Real) (K : Set Space) := rfl

/-- Exact certified outer-box volume of a closed thickening of a slab. -/
theorem IsSlab.volume_closedThickening_le_sideProduct
    {C tau : NNReal} {S : ConvexBody Space}
    (hS : IsSlab C tau S) (r : NNReal) :
    volume (Metric.cthickening (r : Real) (S : Set Space)) ≤
      ((tau : ENNReal) + 2 * (r : ENNReal)) *
        (((1 : ENNReal) + 2 * (r : ENNReal)) ^ 2) := by
  rcases hS with ⟨_htau, _htauUpper, hbox⟩
  rcases hbox with ⟨_hC, B, hBside, _hinner, houter⟩
  have hraw :=
    FamilyStickyConvexClosedThickeningBoxGrowthV1.FrameBox.volume_cthickening_le_prod_side_add_two_mul
      B (S : Set Space) S.isCompact houter r
  rw [hBside] at hraw
  simpa [slabSides, Fin.prod_univ_succ, pow_two] using hraw

/-- The same volume bound at the exact double owner-thickening radius. -/
theorem IsSlab.volume_doubleThetaMulB_closedThickening_le
    {C tau theta b : NNReal} {S : ConvexBody Space}
    (hS : IsSlab C tau S) :
    volume (Metric.cthickening
      (2 * ((theta * b : NNReal) : Real)) (S : Set Space)) ≤
      ((tau : ENNReal) + 4 * ((theta : ENNReal) * (b : ENNReal))) *
        (((1 : ENNReal) +
          4 * ((theta : ENNReal) * (b : ENNReal))) ^ 2) := by
  have h := volume_closedThickening_le_sideProduct hS (2 * (theta * b))
  simp only [NNReal.coe_mul, NNReal.coe_ofNat, ENNReal.coe_mul, ENNReal.coe_ofNat] at h ⊢
  convert h using 1
  all_goals ring

/-- The selected-owner subtype row represented in the original plank index
type, so the original maximal concentration can consume it directly. -/
def activeSelectedOwnerOriginalIndices
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) : Finset iota :=
  (activeSelectedOwnersInCertifiedSlab
    D C q cell hcell selected hmass hactive tau S).map
      ⟨Subtype.val, Subtype.val_injective⟩

theorem activeSelectedOwnerOriginalIndices_card
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space) :
    (activeSelectedOwnerOriginalIndices
      D C q cell hcell selected hmass hactive tau S).card =
      (activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive tau S).card := by
  simp [activeSelectedOwnerOriginalIndices]

/-- Every original selected-owner plank lies in the actual common flat-prism
container. -/
theorem activeSelectedOwnerOriginal_body_subset_closedThickening
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    {tau : NNReal} {S : ConvexBody Space} (hS : IsSlab 1 tau S)
    {s : iota}
    (hs : s ∈ activeSelectedOwnerOriginalIndices
      D C q cell hcell selected hmass hactive tau S) :
    (D.family s : Set Space) ⊆
      Metric.cthickening (2 * ((theta * b : NNReal) : Real))
        (S : Set Space) := by
  classical
  simp only [activeSelectedOwnerOriginalIndices, Finset.mem_map] at hs
  obtain ⟨s', hs', rfl⟩ := hs
  have hself :
      (D.family s'.1 : Set Space) ⊆ ownerThickenedBody D theta s'.1 := by
    simpa only [coe_ownerThickenedBody] using
      (Metric.self_subset_cthickening
        (δ := ((theta * b : NNReal) : Real)) (D.family s'.1 : Set Space))
  exact hself.trans <|
    activeSelectedOwnerThickenedBody_subset_sameSlabThickening
      D C q cell hcell selected hmass hactive hS s' hs'

/-- Family6-style contained-mass count reserve on the actual flat-prism
container.  The left factor is the certified lower volume of one source
plank; the right side is computed from actual maximal concentration and the
certified slab FrameBox. -/
theorem activeSelectedOwners_card_mul_plankVolumeLower_le_flatPrismReserve
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    {tau : NNReal} {S : ConvexBody Space} (hS : IsSlab 1 tau S) :
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive tau S).card : ENNReal) *
        (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) ≤
      maximalConcentration D.family *
        (((tau : ENNReal) +
            4 * ((theta : ENNReal) * (b : ENNReal))) *
          (((1 : ENNReal) +
            4 * ((theta : ENNReal) * (b : ENNReal))) ^ 2)) := by
  classical
  let A := activeSelectedOwnerOriginalIndices
    D C q cell hcell selected hmass hactive tau S
  let K := closedThickeningConvexBody S (2 * (theta * b))
  have hsubset : A ⊆
      Submission.Kakeya.ConvexGeometry.containedIndices D.family K := by
    intro s hs
    apply (mem_containedIndices D.family K s).2
    simpa [K, closedThickeningConvexBody, NNReal.coe_mul] using
      activeSelectedOwnerOriginal_body_subset_closedThickening
        D C q cell hcell selected hmass hactive hS hs
  have hKT : IsKatzTao (maximalConcentration D.family) D.family :=
    isKatzTao_iff_maximalConcentration_le.mpr le_rfl
  calc
    ((activeSelectedOwnersInCertifiedSlab
        D C q cell hcell selected hmass hactive tau S).card : ENNReal) *
        (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) =
      ∑ _s ∈ A,
        (((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3 *
          ((a : ENNReal) * (b : ENNReal))) := by
      rw [← activeSelectedOwnerOriginalIndices_card
        D C q cell hcell selected hmass hactive tau S]
      simp only [A, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ s ∈ A, volume (D.family s : Set Space) := by
      exact Finset.sum_le_sum fun s _hs =>
        (D.all_isPlank s).volume_lower_bound
    _ ≤ ∑ s ∈ Submission.Kakeya.ConvexGeometry.containedIndices D.family K,
        volume (D.family s : Set Space) :=
      Finset.sum_le_sum_of_subset hsubset
    _ = containedMass D.family K := rfl
    _ ≤ maximalConcentration D.family * volume (K : Set Space) := hKT K
    _ ≤ maximalConcentration D.family *
        (((tau : ENNReal) +
            4 * ((theta : ENNReal) * (b : ENNReal))) *
          (((1 : ENNReal) +
            4 * ((theta : ENNReal) * (b : ENNReal))) ^ 2)) := by
      gcongr
      simpa [K, closedThickeningConvexBody, NNReal.coe_mul] using
        IsSlab.volume_doubleThetaMulB_closedThickening_le hS
          (theta := theta) (b := b)

/-! The available owner-fibre mass transport is one-sided: cell restriction
and finite union can only reduce multiplicity-counted mass. -/

theorem activeSelectedOwner_carrier_volume_le_ownerFiberMass
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    {cellIndex : Type v} (cell : cellIndex → Set Space)
    (hcell : ∀ p, MeasurableSet (cell p)) (selected : Finset cellIndex)
    (hmass : (retainedOwnerPlankFamily D C q).shading.shadingMass ≠ 0)
    (hactive : (activeRetainedOwnerCellIndices D C q cell hcell selected).Nonempty)
    (tau : NNReal) (S : ConvexBody Space)
    (s : {s // s ∈ activeSelectedOwnersInCertifiedSlab
      D C q cell hcell selected hmass hactive tau S}) :
    volume ((activeSelectedOwnerSlabShading
      D C q cell hcell selected hmass hactive tau S).carrier s) ≤
        ownerFiberMass C s.1.1 := by
  calc
    volume ((activeSelectedOwnerSlabShading
        D C q cell hcell selected hmass hactive tau S).carrier s) ≤
      volume (ownerFiberInducedCarrier C s.1.1) := by
        apply measure_mono
        intro x hx
        simpa only [activeSelectedOwnerSlabShading_carrier,
          retainedOwnerFinalCoarseShading, restrictToCells_carrier,
          retainedOwnerThickenedShading_carrier] using hx.1
    _ ≤ ownerFiberMass C s.1.1 :=
      ownerFiberInducedCarrier_volume_le_ownerFiberMass C s.1.1

#print axioms coe_closedThickeningConvexBody
#print axioms IsSlab.volume_closedThickening_le_sideProduct
#print axioms IsSlab.volume_doubleThetaMulB_closedThickening_le
#print axioms activeSelectedOwnerOriginal_body_subset_closedThickening
#print axioms activeSelectedOwners_card_mul_plankVolumeLower_le_flatPrismReserve
#print axioms activeSelectedOwner_carrier_volume_le_ownerFiberMass

end
end Family8PlankActiveSelectedOwnerFlatPrismCountV1
