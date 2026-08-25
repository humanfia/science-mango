import FamilyStickyGrounding.FamilyStickyHierarchyPathFirstDivergenceV1

open Set
open scoped BigOperators NNReal

namespace FamilyStickyHierarchySuffixWidenedCollisionRoutingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyActualTubeTranslationV1
open FamilyStickyLatticeMotionRadiusV1
open FamilyStickyMultiscaleSharedMotionCompositionV1
open FamilyStickyMultiscaleSharedMotionCompositionV1.MultiscaleSharedMotionComposition
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyRandomMotionAdapterV1.HierarchyRandomMotionGeometry
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1
open FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1.HierarchyJointRandomMotionCertificate
open FamilyStickyHierarchyPathFirstDivergenceV1

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

/-!
# Cancellation-aware widened routing at the first divergent layer

The later path coordinates cannot be discarded: they may cancel the motion
at the first divergent layer.  This module therefore keeps their literal
sum and its literal radius budget.

For every final occurrence, its final carrier lies in the suffix-radius
closed thickening of the actual prefix-translated layer child.  Equality of
two final carriers consequently gives a common point in the two widened
local carriers, even when the children have different hierarchy parents.
An elementary diameter bound for unit tubes then upgrades that common point
to an honest cross-parent containment with radius

  1 + 2 * layerRadius + 2 * suffixRadius.

No same-parent assertion, global final-index injectivity, or collision
callback is used.
-/

section TubeGeometry

/-- Translating both sides of a carrier inclusion by the same vector
preserves the inclusion, even when the tube radii differ. -/
theorem translateTube_carrier_mono
    {delta epsilon : NNReal} (T : Tube delta) (U : Tube epsilon)
    (hTU : T.carrier ⊆ U.carrier) (v : Space) :
    (translateTube T v).carrier ⊆ (translateTube U v).carrier := by
  rw [translateTube_carrier, translateTube_carrier]
  exact Set.image_mono hTU

/-- The carrier diameter of a radius-`delta` tube around a unit segment is
at most `1 + 2 * delta`. -/
theorem dist_le_one_add_two_mul_radius_of_mem_tube_carrier
    {delta : NNReal} (T : Tube delta) {x y : Space}
    (hx : x ∈ T.carrier) (hy : y ∈ T.carrier) :
    dist x y <= 1 + 2 * (delta : Real) := by
  have hdelta : 0 <= (delta : Real) := by positivity
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall hdelta] at hx hy
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hx hy
  obtain ⟨px, hpx, hxpx⟩ := hx
  obtain ⟨py, hpy, hypy⟩ := hy
  rw [T.axis.carrier_eq_image] at hpx hpy
  obtain ⟨s, hs, rfl⟩ := hpx
  obtain ⟨t, ht, rfl⟩ := hpy
  have hst : |s - t| <= 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hpxty :
      dist (T.axis.base + s • T.axis.direction)
        (T.axis.base + t • T.axis.direction) <= 1 := by
    rw [dist_eq_norm]
    have hsub :
        (T.axis.base + s • T.axis.direction) -
            (T.axis.base + t • T.axis.direction) =
          (s - t) • T.axis.direction := by
      module
    rw [hsub, norm_smul, T.axis.norm_direction, mul_one,
      Real.norm_eq_abs]
    exact hst
  calc
    dist x y <=
        dist x (T.axis.base + s • T.axis.direction) +
          dist (T.axis.base + s • T.axis.direction) y :=
      dist_triangle _ _ _
    _ <= (delta : Real) +
        (dist (T.axis.base + s • T.axis.direction)
            (T.axis.base + t • T.axis.direction) +
          dist (T.axis.base + t • T.axis.direction) y) := by
      gcongr
      exact dist_triangle _ _ _
    _ <= (delta : Real) + (1 + (delta : Real)) := by
      gcongr
      simpa only [dist_comm] using hypy
    _ = 1 + 2 * (delta : Real) := by ring

/-- A point lying within radius `r` of each of two same-radius tubes gives
a deterministic widened containment from the second tube into the first. -/
theorem tube_carrier_subset_cthickening_of_common_widened_point
    {delta r : NNReal} (T U : Tube delta) (x : Space)
    (hxT : x ∈ Metric.cthickening (r : Real) T.carrier)
    (hxU : x ∈ Metric.cthickening (r : Real) U.carrier) :
    U.carrier ⊆
      Metric.cthickening
        ((1 + 2 * delta + 2 * r : NNReal) : Real) T.carrier := by
  have hr : 0 <= (r : Real) := by positivity
  rw [T.isCompact_carrier.cthickening_eq_biUnion_closedBall hr] at hxT
  rw [U.isCompact_carrier.cthickening_eq_biUnion_closedBall hr] at hxU
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hxT hxU
  obtain ⟨zT, hzT, hxzT⟩ := hxT
  obtain ⟨zU, hzU, hxzU⟩ := hxU
  intro y hy
  apply Metric.closedBall_subset_cthickening hzT
  calc
    dist y zT <= dist y zU + dist zU zT := dist_triangle _ _ _
    _ <= dist y zU + (dist zU x + dist x zT) := by
      gcongr
      exact dist_triangle _ _ _
    _ <= (1 + 2 * (delta : Real)) +
        ((r : Real) + (r : Real)) := by
      gcongr
      · exact dist_le_one_add_two_mul_radius_of_mem_tube_carrier U hy hzU
      · simpa only [dist_comm] using hxzU
    _ = ((1 + 2 * delta + 2 * r : NNReal) : Real) := by
      push_cast
      ring

#print axioms translateTube_carrier_mono
#print axioms dist_le_one_add_two_mul_radius_of_mem_tube_carrier
#print axioms tube_carrier_subset_cthickening_of_common_widened_point

end TubeGeometry

section HierarchyRouting

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  (C : HierarchyJointRandomMotionCertificate H G)

/-- Literal sum of all motion coordinates strictly after layer `k`. -/
def suffixVector (path : C.Path) (k : Fin depth) : Space :=
  ∑ i ∈ Finset.univ.filter (fun i => k < i), C.output.omega i (path i)

/-- Literal radius budget of all motion coordinates strictly after layer
`k`.  The current layer motion is already part of the local tube. -/
def suffixRadius (k : Fin depth) : NNReal :=
  ∑ i ∈ Finset.univ.filter (fun i => k < i),
    H.effectiveRadius (i.1 + 1)

theorem norm_suffixVector_le_suffixRadius
    (path : C.Path) (k : Fin depth) :
    ‖suffixVector C path k‖ <= (suffixRadius (H := H) k : Real) := by
  calc
    ‖suffixVector C path k‖ <=
        ∑ i ∈ Finset.univ.filter (fun i => k < i),
          ‖C.output.omega i (path i)‖ := norm_sum_le _ _
    _ <= ∑ i ∈ Finset.univ.filter (fun i => k < i),
        (H.effectiveRadius (i.1 + 1) : Real) := by
      exact Finset.sum_le_sum fun i _ =>
        (C.output.layerOutput i).vector_norm_le (path i)
    _ = (suffixRadius (H := H) k : Real) := by simp [suffixRadius]

/-- The full composed vector is the disjoint sum of the strict prefix, the
current coordinate, and the strict suffix. -/
theorem composedVector_eq_prefix_add_current_add_suffix
    (path : C.Path) (k : Fin depth) :
    C.output.toComposition.composedVector path =
      C.output.prefixVector path k +
        C.output.omega k (path k) + suffixVector C path k := by
  classical
  unfold MultiscaleSharedMotionComposition.composedVector
  unfold FamilyStickyDependentMultiscaleAllParentJointRandomMotionV1.Output.prefixVector
  unfold suffixVector
  calc
    (∑ i, C.output.omega i (path i)) =
        ∑ i, ((if i < k then C.output.omega i (path i) else 0) +
          ((if i = k then C.output.omega i (path i) else 0) +
            (if k < i then C.output.omega i (path i) else 0))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rcases lt_trichotomy i k with hik | hik | hik
      · simp [hik, ne_of_lt hik, not_lt_of_ge (le_of_lt hik)]
      · subst i
        simp
      · simp [hik, ne_of_gt hik, not_lt_of_ge (le_of_lt hik)]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      simp [Finset.sum_filter, add_assoc]

/-- The actual level-`k` ancestor, kept at its native dependent level
`0 + k` so no equality cast is hidden in the geometric proof. -/
def ancestralLayerChild (a : C.FinalIndex) (k : Fin depth) :
    Index (0 + k.1) :=
  H.ancestor 0 k.1 (by omega) a.2.1

/-- The original fine source carrier is nested in its actual layer child. -/
theorem source_carrier_subset_layerChild
    (a : C.FinalIndex) (k : Fin depth) :
    ((H.effectiveFamily 0).tubes a.2.1).carrier ⊆
      ((H.effectiveFamily (0 + k.1)).tubes
        (ancestralLayerChild C a k)).carrier := by
  exact H.effective_carrier_subset_ancestor
    0 k.1 (by omega) a.2.1 a.2.2

/-- Fine source after the current motion and the already accumulated
prefix. -/
def prefixTranslatedFineTube (a : C.FinalIndex) (k : Fin depth) :
    Tube (H.effectiveRadius 0) :=
  translateTube
    (translateTube ((H.effectiveFamily 0).tubes a.2.1)
      (C.output.omega k (a.1 k)))
    (C.output.prefixVector a.1 k)

/-- Actual hierarchy child after the current motion and the same prefix. -/
def prefixTranslatedLayerChild (a : C.FinalIndex) (k : Fin depth) :
    Tube (H.effectiveRadius (0 + k.1)) :=
  translateTube
    (translateTube ((H.effectiveFamily (0 + k.1)).tubes (ancestralLayerChild C a k))
      (C.output.omega k (a.1 k)))
    (C.output.prefixVector a.1 k)

theorem prefixTranslatedFineTube_carrier_subset_layerChild
    (a : C.FinalIndex) (k : Fin depth) :
    (prefixTranslatedFineTube C a k).carrier ⊆
      (prefixTranslatedLayerChild C a k).carrier := by
  apply translateTube_carrier_mono
  apply translateTube_carrier_mono
  exact source_carrier_subset_layerChild C a k

/-- Exact decomposition of a final carrier as the suffix translation of
the prefix-translated fine source. -/
theorem finalTube_carrier_eq_suffixTranslate
    (a : C.FinalIndex) (k : Fin depth) :
    (C.finalTube a).carrier =
      (translateTube (prefixTranslatedFineTube C a k)
        (suffixVector C a.1 k)).carrier := by
  rw [HierarchyJointRandomMotionCertificate.finalTube]
  unfold prefixTranslatedFineTube
  rw [translateTube_translateTube_carrier]
  rw [translateTube_translateTube_carrier]
  rw [composedVector_eq_prefix_add_current_add_suffix C a.1 k]
  congr 2
  module

/-- Every final carrier is contained in the exact suffix-radius widening of
its actual local child. -/
theorem finalTube_carrier_subset_suffixWidenedLayerChild
    (a : C.FinalIndex) (k : Fin depth) :
    (C.finalTube a).carrier ⊆
      Metric.cthickening (suffixRadius (H := H) k : Real)
        (prefixTranslatedLayerChild C a k).carrier := by
  rw [finalTube_carrier_eq_suffixTranslate C a k]
  exact
    (translateTube_carrier_subset_cthickening_of_norm_le
      (prefixTranslatedFineTube C a k) (suffixVector C a.1 k)
      (suffixRadius (H := H) k) (norm_suffixVector_le_suffixRadius C a.1 k)).trans
      (Metric.cthickening_subset_of_subset _
        (prefixTranslatedFineTube_carrier_subset_layerChild C a k))

/-- At the first divergent layer, both local tubes use one literal common
prefix vector. -/
theorem second_prefixTranslatedLayerChild_carrier_eq_commonPrefix
    (a b : C.FinalIndex) (hab : a.1 ≠ b.1) :
    let k := hierarchyFirstDivergenceLayer C a.1 b.1 hab
    (prefixTranslatedLayerChild C b k).carrier =
      (translateTube
        (translateTube ((H.effectiveFamily (0 + k.1)).tubes (ancestralLayerChild C b k))
          (C.output.omega k (b.1 k)))
        (C.output.prefixVector a.1 k)).carrier := by
  dsimp only
  unfold prefixTranslatedLayerChild
  rw [prefixVector_eq_at_hierarchyFirstDivergence C a.1 b.1 hab]

/-- Exact final-carrier equality routes the second final occurrence into
the first local child's suffix widening, without a common-parent claim. -/
theorem equal_finalCarrier_subset_firstDivergence_suffixWidening
    (a b : C.FinalIndex) (hab : a.1 ≠ b.1)
    (hcarrier : (C.finalTube a).carrier = (C.finalTube b).carrier) :
    let k := hierarchyFirstDivergenceLayer C a.1 b.1 hab
    (C.finalTube b).carrier ⊆
      Metric.cthickening (suffixRadius (H := H) k : Real)
        (prefixTranslatedLayerChild C a k).carrier := by
  dsimp only
  rw [← hcarrier]
  exact finalTube_carrier_subset_suffixWidenedLayerChild C a _

/-- The two suffix-widened local child carriers have a literal common point.
Their hierarchy parents may be different. -/
theorem firstDivergence_suffixWidenedLayerChildren_inter_nonempty
    (a b : C.FinalIndex) (hab : a.1 ≠ b.1)
    (hcarrier : (C.finalTube a).carrier = (C.finalTube b).carrier) :
    let k := hierarchyFirstDivergenceLayer C a.1 b.1 hab
    (Metric.cthickening (suffixRadius (H := H) k : Real)
        (prefixTranslatedLayerChild C a k).carrier ∩
      Metric.cthickening (suffixRadius (H := H) k : Real)
        (prefixTranslatedLayerChild C b k).carrier).Nonempty := by
  dsimp only
  let x : Space := (C.finalTube a).axis.base
  have hxA : x ∈ (C.finalTube a).carrier :=
    (C.finalTube a).axis_subset_carrier (C.finalTube a).axis.base_mem_carrier
  refine ⟨x, finalTube_carrier_subset_suffixWidenedLayerChild C a _ hxA, ?_⟩
  apply finalTube_carrier_subset_suffixWidenedLayerChild C b _
  rw [← hcarrier]
  exact hxA

/-- Explicit radius of the cancellation-aware cross-parent widening. -/
def crossParentRoutingRadius (k : Fin depth) : NNReal :=
  1 + 2 * H.effectiveRadius (0 + k.1) + 2 * suffixRadius (H := H) k

/-- Strong cross-parent output: at the first divergent layer, the whole
second local child lies in an explicit widening of the first.  The unit term
and `2 * layerRadius` are the honest diameter cost; `2 * suffixRadius`
accounts for arbitrary later cancellation. -/
theorem firstDivergence_layerChild_carrier_subset_crossParentWidening
    (a b : C.FinalIndex) (hab : a.1 ≠ b.1)
    (hcarrier : (C.finalTube a).carrier = (C.finalTube b).carrier) :
    let k := hierarchyFirstDivergenceLayer C a.1 b.1 hab
    (prefixTranslatedLayerChild C b k).carrier ⊆
      Metric.cthickening (crossParentRoutingRadius (H := H) k : Real)
        (prefixTranslatedLayerChild C a k).carrier := by
  dsimp only
  let k := hierarchyFirstDivergenceLayer C a.1 b.1 hab
  obtain ⟨x, hxA, hxB⟩ :=
    firstDivergence_suffixWidenedLayerChildren_inter_nonempty
      C a b hab hcarrier
  simpa only [crossParentRoutingRadius] using
    tube_carrier_subset_cthickening_of_common_widened_point
      (prefixTranslatedLayerChild C a k)
      (prefixTranslatedLayerChild C b k) x hxA hxB

#print axioms norm_suffixVector_le_suffixRadius
#print axioms composedVector_eq_prefix_add_current_add_suffix
#print axioms source_carrier_subset_layerChild
#print axioms finalTube_carrier_eq_suffixTranslate
#print axioms finalTube_carrier_subset_suffixWidenedLayerChild
#print axioms second_prefixTranslatedLayerChild_carrier_eq_commonPrefix
#print axioms equal_finalCarrier_subset_firstDivergence_suffixWidening
#print axioms firstDivergence_suffixWidenedLayerChildren_inter_nonempty
#print axioms firstDivergence_layerChild_carrier_subset_crossParentWidening

end HierarchyRouting

end

end FamilyStickyHierarchySuffixWidenedCollisionRoutingV1
