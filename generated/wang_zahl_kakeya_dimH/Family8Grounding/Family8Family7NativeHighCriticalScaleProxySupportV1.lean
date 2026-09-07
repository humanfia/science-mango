import Family8Grounding.Family8Family7NativeHighCriticalScaleEndpointBoundsV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyDatumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleProxySupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighCriticalBallDatumV1
open Family8Family7NativeHighCriticalBallRestrictedSourceV1
open Family8Family7NativeHighCriticalBallAffineProxyV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighCriticalScaleProxyDatumV1
open Family8Family7NativeHighCriticalScaleProxySupportCoreV1
open Family8Family7NativeHighCriticalScaleEndpointBoundsV1
open Family8Family7NativeHighNearSaturatedNormSplitV1
open Family8SelectedParentPlankFineProxyDatumV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# Unit-ball support for the concrete native-high critical-scale proxy

The original tube endpoints lie in the unit ball.  The critical metric
controls the `A`, `B`, and `D` gaps, while the common native bucket controls
the `C` gap.  Hence both endpoints map into the quarter ball, and the rich
scale separation places the whole enlarged proxy tube in the unit ball.
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

theorem norm_nativeHighCriticalScaleAffineEquiv_axis_base_le_quarter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (i : NativeHighCriticalBallIndex D c) :
    ‖nativeHighCriticalScaleAffineEquiv D c
        (D.S.family.tubes i.1).axis.base‖ ≤ (1 / 4 : Real) := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  let t := N.criticalScale
  let T0 := D.S.family.tubes N.criticalCenter
  let T := D.S.family.tubes i.1
  have ht : 0 < t := by
    simpa only [N, t] using nativeHighCriticalScale_pos D c
  have hiAmbient : i.1 ∈ D.ambient := datum.subset_physicalAmbient i.2
  have hrefAmbient : N.criticalCenter ∈ D.ambient :=
    datum.subset_physicalAmbient datum.center_mem
  have hCsmall :
      |projectedTubeGraphC T - projectedTubeGraphC T0| ≤
        (radius : Real) / 2 := by
    apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
    · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
    · exact (G.hbucket i.1 hiAmbient).trans
        (G.hbucket N.criticalCenter hrefAmbient).symm
  have hC :
      |projectedTubeGraphC T - projectedTubeGraphC T0| ≤ t := by
    exact hCsmall.trans (by
      have hscale := datum.scale_bounds.1
      change (radius : Real) ≤ t at hscale
      linarith)
  have hdistance := datum.distance_to_center i.1 i.2
  change projectedTubePairCoefficientDistance T T0 ≤ t at hdistance
  have hA : |projectedTubeGraphA T - projectedTubeGraphA T0| ≤ t :=
    abs_projectedTubeGraphA_sub_le_of_pairCoefficientDistance_le hdistance
  have hB : |projectedTubeGraphB T - projectedTubeGraphB T0| ≤ t :=
    abs_projectedTubeGraphB_sub_le_of_pairCoefficientDistance_le hdistance
  have hD : |projectedTubeGraphD T - projectedTubeGraphD T0| ≤ t :=
    abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le hdistance
  have hbaseBall : T.axis.base ∈ Metric.closedBall (0 : Space) 1 := by
    apply datum.contained_in_unit_ball i.1 i.2
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

theorem norm_nativeHighCriticalScaleAffineEquiv_axis_endpoint_le_quarter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source)
    (i : NativeHighCriticalBallIndex D c) :
    ‖nativeHighCriticalScaleAffineEquiv D c
        (D.S.family.tubes i.1).axis.endpoint‖ ≤ (1 / 4 : Real) := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  let t := N.criticalScale
  let T0 := D.S.family.tubes N.criticalCenter
  let T := D.S.family.tubes i.1
  have ht : 0 < t := by
    simpa only [N, t] using nativeHighCriticalScale_pos D c
  have hiAmbient : i.1 ∈ D.ambient := datum.subset_physicalAmbient i.2
  have hrefAmbient : N.criticalCenter ∈ D.ambient :=
    datum.subset_physicalAmbient datum.center_mem
  have hiForwardHalf : (1 / 2 : Real) ≤ |T.axis.direction 2| := by
    apply D.S.source_direction_final_half i.1
    exact hambientSource hiAmbient
  have hiVertical : T.axis.direction 2 ≠ 0 := by
    exact abs_pos.mp (by linarith)
  have hCsmall :
      |projectedTubeGraphC T - projectedTubeGraphC T0| ≤
        (radius : Real) / 2 := by
    apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
    · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
    · exact (G.hbucket i.1 hiAmbient).trans
        (G.hbucket N.criticalCenter hrefAmbient).symm
  have hC :
      |projectedTubeGraphC T - projectedTubeGraphC T0| ≤ t := by
    exact hCsmall.trans (by
      have hscale := datum.scale_bounds.1
      change (radius : Real) ≤ t at hscale
      linarith)
  have hdistance := datum.distance_to_center i.1 i.2
  change projectedTubePairCoefficientDistance T T0 ≤ t at hdistance
  have hA : |projectedTubeGraphA T - projectedTubeGraphA T0| ≤ t :=
    abs_projectedTubeGraphA_sub_le_of_pairCoefficientDistance_le hdistance
  have hB : |projectedTubeGraphB T - projectedTubeGraphB T0| ≤ t :=
    abs_projectedTubeGraphB_sub_le_of_pairCoefficientDistance_le hdistance
  have hD : |projectedTubeGraphD T - projectedTubeGraphD T0| ≤ t :=
    abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le hdistance
  have hendBall : T.axis.endpoint ∈ Metric.closedBall (0 : Space) 1 := by
    apply datum.contained_in_unit_ball i.1 i.2
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

theorem nativeHighCriticalScaleProxyFamily_contained_in_unit_ball_of_richCenter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter}
    (hc : c ∈ nativeHighNearSaturatedCriticalBallRichCenters D G)
    (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source) :
    ∀ i : NativeHighCriticalBallIndex D c,
      (affineAxisProxyTube
        (criticalScaleProxyRadius radius
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)).criticalScale
          (nativeHighCriticalScale_pos D c))
        (nativeHighCriticalScaleAffineEquiv D c)
        (D.S.family.tubes i.1)).carrier ⊆
          Metric.closedBall (0 : Space) 1 := by
  intro i
  apply affineAxisProxyTube_carrier_subset_closedBall_one
    (radius := radius)
    (s := criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c))
    (nativeHighCriticalScaleAffineEquiv D c) (D.S.family.tubes i.1)
  · exact norm_nativeHighCriticalScaleAffineEquiv_axis_base_le_quarter
      D G c datum i
  · exact norm_nativeHighCriticalScaleAffineEquiv_axis_endpoint_le_quarter
      D G c datum hambientSource i
  · exact nativeHighCriticalScaleProxyRadius_le_one_fifth_of_richCenter
      D G hc

#print axioms abs_coordinate_le_one_of_mem_closedBall_one
#print axioms norm_nativeHighCriticalScaleAffineEquiv_axis_base_le_quarter
#print axioms norm_nativeHighCriticalScaleAffineEquiv_axis_endpoint_le_quarter
#print axioms nativeHighCriticalScaleProxyFamily_contained_in_unit_ball_of_richCenter

end

end Family8Family7NativeHighCriticalScaleProxySupportV1
