import Family8Grounding.Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleEndpointBoundsV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxySupportCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighArbitraryWeightedProxySupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleEndpointBoundsV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighCriticalScaleProxySupportCoreV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8SelectedParentPlankFineProxyDatumV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1

noncomputable section

universe u

/-!
# Unit-ball support for an arbitrary weighted native-high proxy

The proof uses no special property of the occurrence weight.  The critical
metric controls the `A`, `B`, and `D` gaps, the native bucket controls the `C`
gap, and upstream unit-ball support controls the last coordinate.  Thus a
single explicit proxy-radius cap upgrades the arbitrary weighted proxy to the
unit-ball support required by the direct greedy admissibility theorem.
-/

theorem abs_coordinate_le_one_of_mem_closedBall_one
    (p : Space) (hp : p ∈ Metric.closedBall (0 : Space) 1)
    (j : Fin 3) :
    |p j| ≤ 1 := by
  rw [Metric.mem_closedBall, dist_zero_right] at hp
  calc
    |p j| ≤ ‖p‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p j
    _ ≤ 1 := hp

theorem norm_nativeHighArbitraryWeightedAffineEquiv_axis_base_le_quarter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (W : NativeHighArbitraryWeightedProxyInput D)
    (hcontained : ∀ i, i ∈ D.ambient →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (i : NativeHighArbitraryWeightedCriticalBallIndex D W) :
    ‖nativeHighArbitraryWeightedCriticalScaleAffineEquiv D W
        (D.S.family.tubes i.1).axis.base‖ ≤ (1 / 4 : Real) := by
  let N := nativeHighWeightedNormData D W.center W.weight
  let t := N.criticalScale
  let T0 := D.S.family.tubes N.criticalCenter
  let T := D.S.family.tubes i.1
  have ht : 0 < t := by
    simpa only [N, t] using
      nativeHighArbitraryWeightedCriticalScale_pos D W
  have hiAmbient : i.1 ∈ D.ambient :=
    nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient D W i.2
  have hrefAmbient : N.criticalCenter ∈ D.ambient :=
    nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient D W
      N.criticalCenter_mem_criticalBall
  have hCsmall :
      |projectedTubeGraphC T - projectedTubeGraphC T0| ≤
        (radius : Real) / 2 := by
    apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
    · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
    · exact (W.geometry.hbucket i.1 hiAmbient).trans
        (W.geometry.hbucket N.criticalCenter hrefAmbient).symm
  have hC :
      |projectedTubeGraphC T - projectedTubeGraphC T0| ≤ t := by
    exact hCsmall.trans (by
      have hscale := N.criticalScale_bounds.1
      change (radius : Real) ≤ t at hscale
      linarith)
  have hdistance := N.criticalBall_distance_to_center i.2
  change projectedTubePairCoefficientDistance T T0 ≤ t at hdistance
  have hA : |projectedTubeGraphA T - projectedTubeGraphA T0| ≤ t :=
    abs_projectedTubeGraphA_sub_le_of_pairCoefficientDistance_le hdistance
  have hB : |projectedTubeGraphB T - projectedTubeGraphB T0| ≤ t :=
    abs_projectedTubeGraphB_sub_le_of_pairCoefficientDistance_le hdistance
  have hD : |projectedTubeGraphD T - projectedTubeGraphD T0| ≤ t :=
    abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le hdistance
  have hbaseBall : T.axis.base ∈ Metric.closedBall (0 : Space) 1 := by
    apply hcontained i.1 hiAmbient
    exact T.axis_subset_carrier T.axis.base_mem_carrier
  have hbase2 : |T.axis.base 2| ≤ 1 :=
    abs_coordinate_le_one_of_mem_closedBall_one T.axis.base hbaseBall 2
  change ‖criticalScaleAffineEquiv t ht
    (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0) T.axis.base‖ ≤
      (1 / 4 : Real)
  exact norm_criticalScaleAffineEquiv_apply_le_quarter_of_graph_gaps
    t ht T T0 T.axis.base
      (tube_axis_base_graphC_coordinate T)
      (tube_axis_base_graphD_coordinate T) hbase2 hA hB hC hD

theorem norm_nativeHighArbitraryWeightedAffineEquiv_axis_endpoint_le_quarter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (W : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source)
    (hcontained : ∀ i, i ∈ D.ambient →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (i : NativeHighArbitraryWeightedCriticalBallIndex D W) :
    ‖nativeHighArbitraryWeightedCriticalScaleAffineEquiv D W
        (D.S.family.tubes i.1).axis.endpoint‖ ≤ (1 / 4 : Real) := by
  let N := nativeHighWeightedNormData D W.center W.weight
  let t := N.criticalScale
  let T0 := D.S.family.tubes N.criticalCenter
  let T := D.S.family.tubes i.1
  have ht : 0 < t := by
    simpa only [N, t] using
      nativeHighArbitraryWeightedCriticalScale_pos D W
  have hiAmbient : i.1 ∈ D.ambient :=
    nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient D W i.2
  have hrefAmbient : N.criticalCenter ∈ D.ambient :=
    nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient D W
      N.criticalCenter_mem_criticalBall
  have hiForwardHalf : (1 / 2 : Real) ≤ |T.axis.direction 2| := by
    apply D.S.source_direction_final_half i.1
    exact hambientSource hiAmbient
  have hiVertical : T.axis.direction 2 ≠ 0 :=
    abs_pos.mp (by linarith)
  have hCsmall :
      |projectedTubeGraphC T - projectedTubeGraphC T0| ≤
        (radius : Real) / 2 := by
    apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
    · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
    · exact (W.geometry.hbucket i.1 hiAmbient).trans
        (W.geometry.hbucket N.criticalCenter hrefAmbient).symm
  have hC :
      |projectedTubeGraphC T - projectedTubeGraphC T0| ≤ t := by
    exact hCsmall.trans (by
      have hscale := N.criticalScale_bounds.1
      change (radius : Real) ≤ t at hscale
      linarith)
  have hdistance := N.criticalBall_distance_to_center i.2
  change projectedTubePairCoefficientDistance T T0 ≤ t at hdistance
  have hA : |projectedTubeGraphA T - projectedTubeGraphA T0| ≤ t :=
    abs_projectedTubeGraphA_sub_le_of_pairCoefficientDistance_le hdistance
  have hB : |projectedTubeGraphB T - projectedTubeGraphB T0| ≤ t :=
    abs_projectedTubeGraphB_sub_le_of_pairCoefficientDistance_le hdistance
  have hD : |projectedTubeGraphD T - projectedTubeGraphD T0| ≤ t :=
    abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le hdistance
  have hendBall : T.axis.endpoint ∈ Metric.closedBall (0 : Space) 1 := by
    apply hcontained i.1 hiAmbient
    exact T.axis_subset_carrier T.axis.endpoint_mem_carrier
  have hend2 : |T.axis.endpoint 2| ≤ 1 :=
    abs_coordinate_le_one_of_mem_closedBall_one T.axis.endpoint hendBall 2
  change ‖criticalScaleAffineEquiv t ht
    (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0) T.axis.endpoint‖ ≤
      (1 / 4 : Real)
  exact norm_criticalScaleAffineEquiv_apply_le_quarter_of_graph_gaps
    t ht T T0 T.axis.endpoint
      (tube_axis_endpoint_graphC_coordinate T hiVertical)
      (tube_axis_endpoint_graphD_coordinate T hiVertical)
      hend2 hA hB hC hD

theorem nativeHighArbitraryWeightedProxyFamily_contained_in_unit_ball
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (W : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source)
    (hcontained : ∀ i, i ∈ D.ambient →
      (D.S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hproxyRadius :
      criticalScaleProxyRadius radius
          (nativeHighWeightedNormData D W.center W.weight).criticalScale
          (nativeHighArbitraryWeightedCriticalScale_pos D W) ≤
        (1 / 5 : NNReal)) :
    ∀ i : NativeHighArbitraryWeightedCriticalBallIndex D W,
      ((nativeHighArbitraryWeightedCriticalScaleProxyFamily
        D W).tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
  intro i
  change (affineAxisProxyTube
    (criticalScaleProxyRadius radius
      (nativeHighWeightedNormData D W.center W.weight).criticalScale
      (nativeHighArbitraryWeightedCriticalScale_pos D W))
    (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D W)
    (D.S.family.tubes i.1)).carrier ⊆ Metric.closedBall (0 : Space) 1
  apply affineAxisProxyTube_carrier_subset_closedBall_one
    (radius := radius)
    (s := criticalScaleProxyRadius radius
      (nativeHighWeightedNormData D W.center W.weight).criticalScale
      (nativeHighArbitraryWeightedCriticalScale_pos D W))
    (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D W)
    (D.S.family.tubes i.1)
  · exact norm_nativeHighArbitraryWeightedAffineEquiv_axis_base_le_quarter
      D W hcontained i
  · exact
      norm_nativeHighArbitraryWeightedAffineEquiv_axis_endpoint_le_quarter
        D W hambientSource hcontained i
  · exact hproxyRadius

#print axioms abs_coordinate_le_one_of_mem_closedBall_one
#print axioms norm_nativeHighArbitraryWeightedAffineEquiv_axis_base_le_quarter
#print axioms
  norm_nativeHighArbitraryWeightedAffineEquiv_axis_endpoint_le_quarter
#print axioms nativeHighArbitraryWeightedProxyFamily_contained_in_unit_ball

end

end Family8Family7NativeHighArbitraryWeightedProxySupportV1
