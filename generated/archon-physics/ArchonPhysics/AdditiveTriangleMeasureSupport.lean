import ArchonPhysics.ContinuousThreeWaveBalanceRigidity
import Mathlib.Analysis.Convex.Topology

/-!
# Lebesgue trace criteria for full additive-triangle support

This module turns a model-specific on-shell trace statement into the exact
topological support premise used by continuous three-wave balance rigidity.

The reference measure is two-dimensional Lebesgue measure restricted to the
closed additive triangle.  Every point of the triangle, including its three
boundary faces, lies in the support of this restriction.  Consequently it is
enough to prove that this reference trace is absolutely continuous with
respect to the target child-frequency-pair measure.  This is the null-set
direction supplied by an almost-everywhere strictly positive on-shell density.
-/

namespace ArchonPhysics.AdditiveTriangleMeasureSupport

open Set MeasureTheory
open ArchonPhysics.ContinuousThreeWaveBalanceRigidity

noncomputable section

/-- The strict interior inequalities corresponding to the additive frequency
triangle. -/
def strictAdditiveFrequencyTriangle (W : Real) : Set (Real × Real) :=
  {pair | 0 < pair.1 ∧ 0 < pair.2 ∧ pair.1 + pair.2 < W}

theorem isOpen_strictAdditiveFrequencyTriangle (W : Real) :
    IsOpen (strictAdditiveFrequencyTriangle W) := by
  rw [show strictAdditiveFrequencyTriangle W =
      {p : Real × Real | 0 < p.1} ∩
        ({p : Real × Real | 0 < p.2} ∩
          {p : Real × Real | p.1 + p.2 < W}) by
    ext p
    simp only [strictAdditiveFrequencyTriangle, mem_ofPred_eq, mem_inter_iff]]
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))

theorem strictAdditiveFrequencyTriangle_subset (W : Real) :
    strictAdditiveFrequencyTriangle W ⊆ additiveFrequencyTriangle W := by
  intro p hp
  exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

/-- The closed additive frequency triangle is convex. -/
theorem convex_additiveFrequencyTriangle (W : Real) :
    Convex Real (additiveFrequencyTriangle W) := by
  intro x hx y hy a b ha hb hab
  simp only [additiveFrequencyTriangle, mem_ofPred_eq] at hx hy ⊢
  constructor
  · change 0 ≤ a * x.1 + b * y.1
    exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  constructor
  · change 0 ≤ a * x.2 + b * y.2
    exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
  · change (a * x.1 + b * y.1) + (a * x.2 + b * y.2) ≤ W
    calc
      (a * x.1 + b * y.1) + (a * x.2 + b * y.2) =
          a * (x.1 + x.2) + b * (y.1 + y.2) := by ring
      _ ≤ a * W + b * W :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
          (mul_le_mul_of_nonneg_left hy.2.2 hb)
      _ = W := by rw [← add_mul, hab, one_mul]

/-- A positive-width additive triangle has nonempty ordinary interior. -/
theorem interior_additiveFrequencyTriangle_nonempty
    {W : Real} (hW : 0 < W) :
    (interior (additiveFrequencyTriangle W)).Nonempty := by
  let p : Real × Real := (W / 4, W / 4)
  have hpStrict : p ∈ strictAdditiveFrequencyTriangle W := by
    dsimp [p, strictAdditiveFrequencyTriangle]
    constructor
    · positivity
    constructor
    · positivity
    · linarith
  refine ⟨p, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset
    ((isOpen_strictAdditiveFrequencyTriangle W).mem_nhds hpStrict)
    (strictAdditiveFrequencyTriangle_subset W)

/-- Two-dimensional Lebesgue measure restricted to a positive-width additive
triangle has the whole closed triangle in its support, including boundary
points. -/
theorem additiveFrequencyTriangle_subset_volume_restrict_support
    {W : Real} (hW : 0 < W) :
    additiveFrequencyTriangle W ⊆
      (volume.restrict (additiveFrequencyTriangle W)).support := by
  have hinterior : interior (additiveFrequencyTriangle W) ⊆
      (volume.restrict (additiveFrequencyTriangle W)).support := by
    intro x hx
    apply Measure.interior_inter_support
    refine ⟨hx, ?_⟩
    rw [Measure.support_eq_univ]
    trivial
  have hclosure : closure (interior (additiveFrequencyTriangle W)) ⊆
      (volume.restrict (additiveFrequencyTriangle W)).support :=
    Measure.isClosed_support.closure_subset_iff.mpr hinterior
  have hclosureInterior :
      closure (interior (additiveFrequencyTriangle W)) =
        closure (additiveFrequencyTriangle W) :=
    (convex_additiveFrequencyTriangle W).closure_interior_eq_closure_of_nonempty_interior
      (interior_additiveFrequencyTriangle_nonempty hW)
  rw [hclosureInterior] at hclosure
  exact subset_closure.trans hclosure

/-- A model-specific on-shell trace which dominates Lebesgue null sets has
the exact relative full support required by the continuous rigidity theorem.

The direction of `≪` is deliberate: a target-null set must be
Lebesgue-null. -/
theorem fullSupport_of_volume_absolutelyContinuous
    {W : Real} (hW : 0 < W) {pairMeasure : Measure (Real × Real)}
    (htrace : volume.restrict (additiveFrequencyTriangle W) ≪
      pairMeasure.restrict (additiveFrequencyTriangle W)) :
    additiveFrequencyTriangle W ⊆
      (pairMeasure.restrict (additiveFrequencyTriangle W)).support := by
  exact (additiveFrequencyTriangle_subset_volume_restrict_support hW).trans
    htrace.support_mono

end

end ArchonPhysics.AdditiveTriangleMeasureSupport
