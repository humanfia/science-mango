import Family8Grounding.Family8Family7NativeHighCriticalScaleProxySupportCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleEndpointBoundsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8SelectedParentPlankFineProxyCarrierV3
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-!
# Endpoint bounds for the concrete critical-scale map

The reduced metric controls the `A`, `B`, and `D` gaps; the native bucket
will supply the `C` gap.  This file isolates the sign-free coordinate
calculation showing that either endpoint maps into `B(0,1/4)`.
-/

theorem abs_projectedTubeGraphA_sub_le_of_pairCoefficientDistance_le
    {radius : NNReal} {T U : Tube radius} {t : Real}
    (hTU : projectedTubePairCoefficientDistance T U ≤ t) :
    |projectedTubeGraphA T - projectedTubeGraphA U| ≤ t := by
  unfold projectedTubePairCoefficientDistance
    FamilyStickyCinematicL32LocalTangencyV1.coefficientDistance
    projectedTubePairDeltaA projectedTubePairDeltaB projectedTubePairDeltaD
    at hTU
  nlinarith [abs_nonneg
    (projectedTubeGraphB T - projectedTubeGraphB U),
    abs_nonneg (projectedTubeGraphD T - projectedTubeGraphD U)]

theorem abs_projectedTubeGraphB_sub_le_of_pairCoefficientDistance_le
    {radius : NNReal} {T U : Tube radius} {t : Real}
    (hTU : projectedTubePairCoefficientDistance T U ≤ t) :
    |projectedTubeGraphB T - projectedTubeGraphB U| ≤ t := by
  unfold projectedTubePairCoefficientDistance
    FamilyStickyCinematicL32LocalTangencyV1.coefficientDistance
    projectedTubePairDeltaA projectedTubePairDeltaB projectedTubePairDeltaD
    at hTU
  nlinarith [abs_nonneg
    (projectedTubeGraphA T - projectedTubeGraphA U),
    abs_nonneg (projectedTubeGraphD T - projectedTubeGraphD U)]

theorem tube_axis_base_graphC_coordinate
    {radius : NNReal} (T : Tube radius) :
    T.axis.base 0 =
      projectedTubeGraphA T + projectedTubeGraphC T * T.axis.base 2 := by
  unfold projectedTubeGraphA
  ring

theorem tube_axis_base_graphD_coordinate
    {radius : NNReal} (T : Tube radius) :
    T.axis.base 1 =
      projectedTubeGraphB T + projectedTubeGraphD T * T.axis.base 2 := by
  unfold projectedTubeGraphB
  ring

theorem tube_axis_endpoint_graphC_coordinate
    {radius : NNReal} (T : Tube radius)
    (hvertical : T.axis.direction 2 ≠ 0) :
    T.axis.endpoint 0 =
      projectedTubeGraphA T + projectedTubeGraphC T * T.axis.endpoint 2 := by
  have hdirection : T.axis.direction 0 =
      projectedTubeGraphC T * T.axis.direction 2 := by
    unfold projectedTubeGraphC
    field_simp [hvertical]
  unfold UnitSegment.endpoint
  simp only [PiLp.add_apply]
  rw [tube_axis_base_graphC_coordinate T, hdirection]
  ring

theorem tube_axis_endpoint_graphD_coordinate
    {radius : NNReal} (T : Tube radius)
    (hvertical : T.axis.direction 2 ≠ 0) :
    T.axis.endpoint 1 =
      projectedTubeGraphB T + projectedTubeGraphD T * T.axis.endpoint 2 := by
  have hdirection : T.axis.direction 1 =
      projectedTubeGraphD T * T.axis.direction 2 := by
    unfold projectedTubeGraphD
    field_simp [hvertical]
  unfold UnitSegment.endpoint
  simp only [PiLp.add_apply]
  rw [tube_axis_base_graphD_coordinate T, hdirection]
  ring

theorem norm_criticalScaleAffineEquiv_apply_le_quarter_of_coordinate_bounds
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real) (p : Space)
    (hx : |p 0 - a0 - c0 * p 2| ≤ 2 * t)
    (hy : |p 1 - b0 - d0 * p 2| ≤ 2 * t)
    (hz : |p 2| ≤ 1) :
    ‖criticalScaleAffineEquiv t ht a0 b0 c0 d0 p‖ ≤
      (1 / 4 : Real) := by
  have hden : 0 < 16 * t := mul_pos (by norm_num) ht
  have hx' : |(p 0 - a0 - c0 * p 2) / (16 * t)| ≤
      (1 / 8 : Real) := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hy' : |(p 1 - b0 - d0 * p 2) / (16 * t)| ≤
      (1 / 8 : Real) := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hz' : |p 2 / 16| ≤ (1 / 16 : Real) := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 16)]
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 16)).2
    nlinarith
  have hxsq := (sq_le_sq₀ (abs_nonneg _)
    (by norm_num : (0 : Real) ≤ 1 / 8)).2 hx'
  have hysq := (sq_le_sq₀ (abs_nonneg _)
    (by norm_num : (0 : Real) ≤ 1 / 8)).2 hy'
  have hzsq := (sq_le_sq₀ (abs_nonneg _)
    (by norm_num : (0 : Real) ≤ 1 / 16)).2 hz'
  rw [criticalScaleAffineEquiv_apply]
  apply (sq_le_sq₀ (norm_nonneg _)
    (by norm_num : (0 : Real) ≤ 1 / 4)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  change
    ((p 0 - a0 - c0 * p 2) / (16 * t)) ^ 2 +
      ((p 1 - b0 - d0 * p 2) / (16 * t)) ^ 2 +
      (p 2 / 16) ^ 2 ≤ (1 / 4 : Real) ^ 2
  norm_num at hxsq hysq hzsq ⊢
  nlinarith

theorem norm_criticalScaleAffineEquiv_apply_le_quarter_of_graph_gaps
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (T T0 : Tube radius) (p : Space)
    (hpC : p 0 =
      projectedTubeGraphA T + projectedTubeGraphC T * p 2)
    (hpD : p 1 =
      projectedTubeGraphB T + projectedTubeGraphD T * p 2)
    (hp2 : |p 2| ≤ 1)
    (hA : |projectedTubeGraphA T - projectedTubeGraphA T0| ≤ t)
    (hB : |projectedTubeGraphB T - projectedTubeGraphB T0| ≤ t)
    (hC : |projectedTubeGraphC T - projectedTubeGraphC T0| ≤ t)
    (hD : |projectedTubeGraphD T - projectedTubeGraphD T0| ≤ t) :
    ‖criticalScaleAffineEquiv t ht
      (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0) p‖ ≤
        (1 / 4 : Real) := by
  have hx :
      |p 0 - projectedTubeGraphA T0 - projectedTubeGraphC T0 * p 2| ≤
        2 * t := by
    rw [hpC]
    have htriangle := abs_add_le
      (projectedTubeGraphA T - projectedTubeGraphA T0)
      ((projectedTubeGraphC T - projectedTubeGraphC T0) * p 2)
    calc
      |projectedTubeGraphA T + projectedTubeGraphC T * p 2 -
          projectedTubeGraphA T0 - projectedTubeGraphC T0 * p 2| =
        |(projectedTubeGraphA T - projectedTubeGraphA T0) +
          (projectedTubeGraphC T - projectedTubeGraphC T0) * p 2| := by
            congr 1
            ring
      _ ≤ |projectedTubeGraphA T - projectedTubeGraphA T0| +
          |(projectedTubeGraphC T - projectedTubeGraphC T0) * p 2| :=
        htriangle
      _ = |projectedTubeGraphA T - projectedTubeGraphA T0| +
          |projectedTubeGraphC T - projectedTubeGraphC T0| * |p 2| := by
        rw [abs_mul]
      _ ≤ t + t * 1 := by gcongr
      _ = 2 * t := by ring
  have hy :
      |p 1 - projectedTubeGraphB T0 - projectedTubeGraphD T0 * p 2| ≤
        2 * t := by
    rw [hpD]
    have htriangle := abs_add_le
      (projectedTubeGraphB T - projectedTubeGraphB T0)
      ((projectedTubeGraphD T - projectedTubeGraphD T0) * p 2)
    calc
      |projectedTubeGraphB T + projectedTubeGraphD T * p 2 -
          projectedTubeGraphB T0 - projectedTubeGraphD T0 * p 2| =
        |(projectedTubeGraphB T - projectedTubeGraphB T0) +
          (projectedTubeGraphD T - projectedTubeGraphD T0) * p 2| := by
            congr 1
            ring
      _ ≤ |projectedTubeGraphB T - projectedTubeGraphB T0| +
          |(projectedTubeGraphD T - projectedTubeGraphD T0) * p 2| :=
        htriangle
      _ = |projectedTubeGraphB T - projectedTubeGraphB T0| +
          |projectedTubeGraphD T - projectedTubeGraphD T0| * |p 2| := by
        rw [abs_mul]
      _ ≤ t + t * 1 := by gcongr
      _ = 2 * t := by ring
  exact norm_criticalScaleAffineEquiv_apply_le_quarter_of_coordinate_bounds
    t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0) p hx hy hp2

#print axioms abs_projectedTubeGraphA_sub_le_of_pairCoefficientDistance_le
#print axioms abs_projectedTubeGraphB_sub_le_of_pairCoefficientDistance_le
#print axioms tube_axis_base_graphC_coordinate
#print axioms tube_axis_base_graphD_coordinate
#print axioms tube_axis_endpoint_graphC_coordinate
#print axioms tube_axis_endpoint_graphD_coordinate
#print axioms norm_criticalScaleAffineEquiv_apply_le_quarter_of_coordinate_bounds
#print axioms norm_criticalScaleAffineEquiv_apply_le_quarter_of_graph_gaps

end

end Family8Family7NativeHighCriticalScaleEndpointBoundsV1
