import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import FamilyStickyGrounding.FamilyStickyHierarchySuffixWidenedCollisionRoutingV1
import Mathlib.Tactic

/-!
# Uniform mass cap for zero-twisted fibres of actual unit tubes

The canonical graph route uses the full fibre window `Set.univ`, so the
generic window-volume cap is unavailable.  For its literal zero twisted
projection there is nevertheless a geometric cap: the fibre chart is an
isometric copy of the second coordinate, while every shading carrier lies in
a radius-`delta` tube around a unit segment.  Hence each one-dimensional
fibre mass is at most `1 + 2 * delta`, and at most `2` when `delta <= 1/2`.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8UniformTubeZeroFibreMassCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyHierarchySuffixWidenedCollisionRoutingV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-- The zero-twisted fibre chart preserves the distance between fibre
coordinates. -/
theorem dist_twistedFiberChart_zero
    (u : ProjectionSpace) (y z : Real) :
    dist (twistedFiberChart (fun _ => 0) (u, y))
      (twistedFiberChart (fun _ => 0) (u, z)) = dist y z := by
  rw [dist_eq_norm, dist_eq_norm]
  simp [twistedFiberChart, point3, EuclideanSpace.norm_eq,
    Fin.sum_univ_succ, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

/-- Every zero-twisted fibre of a shading of radius-`delta` unit tubes has
mass at most the tube diameter `1 + 2 * delta`.  This does not use a bounded
fibre window. -/
theorem shadingFiberMass_zero_le_one_add_two_radius
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (i : iota) (u : ProjectionSpace) :
    shadingFiberMass Y (fun _ => 0) i u <=
      ENNReal.ofReal (1 + 2 * (delta : Real)) := by
  let S : Set Real :=
    {y | twistedFiberChart (fun _ => 0) (u, y) ∈ Y.carrier i}
  have hchart : Continuous
      (fun y : Real => twistedFiberChart (fun _ => 0) (u, y)) := by
    unfold twistedFiberChart point3
    fun_prop
  have hS : MeasurableSet S :=
    (Y.measurable_carrier i).preimage hchart.measurable
  have hmass : shadingFiberMass Y (fun _ => 0) i u = volume S := by
    unfold shadingFiberMass
    change (∫⁻ y : Real, S.indicator (fun _ => (1 : ENNReal)) y ∂volume) =
      volume S
    exact lintegral_indicator_one hS
  rw [hmass]
  refine (Real.volume_le_diam S).trans ?_
  apply (Metric.ediam_le_iff).2
  intro y hy z hz
  have hyTube : twistedFiberChart (fun _ => 0) (u, y) ∈
      (fine.tubes i).carrier := Y.carrier_subset i hy
  have hzTube : twistedFiberChart (fun _ => 0) (u, z) ∈
      (fine.tubes i).carrier := Y.carrier_subset i hz
  have hdist :=
    dist_le_one_add_two_mul_radius_of_mem_tube_carrier
      (fine.tubes i) hyTube hzTube
  have hyz : dist y z <= 1 + 2 * (delta : Real) := by
    rw [← dist_twistedFiberChart_zero u y z]
    exact hdist
  simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hyz

/-- At the scale range used by the canonical graph, the preceding cap is the
fixed constant two. -/
theorem shadingFiberMass_zero_le_two
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota)
    (Y : Shading fine.bodyFamily) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (i : iota) (u : ProjectionSpace) :
    shadingFiberMass Y (fun _ => 0) i u <= 2 := by
  calc
    shadingFiberMass Y (fun _ => 0) i u <=
        ENNReal.ofReal (1 + 2 * (delta : Real)) :=
      shadingFiberMass_zero_le_one_add_two_radius fine Y i u
    _ <= ENNReal.ofReal 2 := by
      apply ENNReal.ofReal_le_ofReal
      have hdeltaReal : (delta : Real) <=
          (((2 : NNReal)⁻¹ : NNReal) : Real) := by
        exact_mod_cast hdeltaHalf
      norm_num at hdeltaReal
      linarith
    _ = 2 := by norm_num

#print axioms dist_twistedFiberChart_zero
#print axioms shadingFiberMass_zero_le_one_add_two_radius
#print axioms shadingFiberMass_zero_le_two

end
end Family8UniformTubeZeroFibreMassCapV1
