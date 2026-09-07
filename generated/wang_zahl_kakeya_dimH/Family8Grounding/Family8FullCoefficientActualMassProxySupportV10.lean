import Family8Grounding.Family8FullCoefficientActualMassProxyGeometryV7
import Family8Grounding.Family8Family7NativeHighCriticalScaleEndpointBoundsV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxySupportCoreV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxySupportV1
import Mathlib.Tactic

/-!
# Automatic unit-ball support for the ten-radius full-coefficient proxy, V10

This clean ADD-only successor uses the authoritative CriticalScale V5 and
Geometry V7 chain.  The elementary closed-ball coordinate estimate is cited
from its authoritative Family7 owner with a fully qualified name.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FullCoefficientActualMassProxySupportV10

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleEndpointBoundsV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighCriticalScaleProxySupportCoreV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8FullCoefficientActualMassProxyGeometryV7
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

private theorem norm_fullCoefficientAffineEquiv_apply_le_quarter
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (i : {i // i ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).criticalBall})
    (p : Space)
    (hpC : p 0 =
      projectedTubeGraphA (S.family.tubes i.1) +
        projectedTubeGraphC (S.family.tubes i.1) * p 2)
    (hpD : p 1 =
      projectedTubeGraphB (S.family.tubes i.1) +
        projectedTubeGraphD (S.family.tubes i.1) * p 2)
    (hpBall : p ∈ Metric.closedBall (0 : Space) 1) :
    ‖weightedCanonicalCriticalScaleAffineEquiv S
        (fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y X) p‖ ≤ (1 / 4 : Real) := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  let t := W.criticalScale
  let T0 := S.family.tubes W.criticalCenter
  let T := S.family.tubes i.1
  have ht : 0 < t := weightedCanonicalCriticalScale_pos W
  have hp2 : |p 2| ≤ 1 :=
    Family8Family7NativeHighCriticalScaleProxySupportV1.abs_coordinate_le_one_of_mem_closedBall_one
      p hpBall 2
  change ‖criticalScaleAffineEquiv t ht
    (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0) p‖ ≤
      (1 / 4 : Real)
  exact norm_criticalScaleAffineEquiv_apply_le_quarter_of_graph_gaps
    t ht T T0 p hpC hpD hp2
      (fullCoefficient_criticalBall_graphA_gap S active hactive hradius
        htenRadiusSixteen Y X i.2)
      (fullCoefficient_criticalBall_graphB_gap S active hactive hradius
        htenRadiusSixteen Y X i.2)
      (fullCoefficient_criticalBall_graphC_gap S active hactive hradius
        htenRadiusSixteen Y X i.2)
      (fullCoefficient_criticalBall_graphD_gap S active hactive hradius
        htenRadiusSixteen Y X i.2)

private theorem norm_fullCoefficientAffineEquiv_axis_base_le_quarter
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (i : {i // i ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).criticalBall}) :
    ‖weightedCanonicalCriticalScaleAffineEquiv S
        (fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y X)
          (S.family.tubes i.1).axis.base‖ ≤ (1 / 4 : Real) := by
  apply norm_fullCoefficientAffineEquiv_apply_le_quarter
    S active hactive hradius htenRadiusSixteen Y X i
  · exact tube_axis_base_graphC_coordinate (S.family.tubes i.1)
  · exact tube_axis_base_graphD_coordinate (S.family.tubes i.1)
  · apply hcontained i.1
    · exact (fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X).criticalBall_subset_family i.2
    · exact (S.family.tubes i.1).axis_subset_carrier
        (S.family.tubes i.1).axis.base_mem_carrier

private theorem norm_fullCoefficientAffineEquiv_axis_endpoint_le_quarter
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (i : {i // i ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).criticalBall}) :
    ‖weightedCanonicalCriticalScaleAffineEquiv S
        (fullCoefficientActualMassNormData S active hactive
          hradius htenRadiusSixteen Y X)
          (S.family.tubes i.1).axis.endpoint‖ ≤ (1 / 4 : Real) := by
  have hiActive : i.1 ∈ active :=
    (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).criticalBall_subset_family i.2
  have hiForwardHalf := S.source_direction_final_half i.1
    (hactiveSource hiActive)
  have hiVertical : (S.family.tubes i.1).axis.direction 2 ≠ 0 :=
    abs_pos.mp (by linarith)
  apply norm_fullCoefficientAffineEquiv_apply_le_quarter
    S active hactive hradius htenRadiusSixteen Y X i
  · exact tube_axis_endpoint_graphC_coordinate
      (S.family.tubes i.1) hiVertical
  · exact tube_axis_endpoint_graphD_coordinate
      (S.family.tubes i.1) hiVertical
  · exact hcontained i.1 hiActive
      ((S.family.tubes i.1).axis_subset_carrier
        (S.family.tubes i.1).axis.endpoint_mem_carrier)

/-- Tenfold separation gives the proxy-radius caps and literal unit-ball
support for the full-coefficient actual-mass critical ball. -/
theorem fullCoefficientActualMass_proxySupport
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    criticalScaleProxyRadius radius W.criticalScale
        (weightedCanonicalCriticalScale_pos W) ≤ (1 / 5 : NNReal) ∧
      criticalScaleProxyRadius radius W.criticalScale
        (weightedCanonicalCriticalScale_pos W) ≤ (2 : NNReal)⁻¹ ∧
      ∀ i : {i // i ∈ W.criticalBall},
        ((weightedCanonicalCriticalScaleProxyFamily S W).tubes i).carrier ⊆
          Metric.closedBall (0 : Space) 1 := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  have hproxyFifth : criticalScaleProxyRadius radius W.criticalScale
      (weightedCanonicalCriticalScale_pos W) ≤ (1 / 5 : NNReal) :=
    criticalScaleProxyRadius_le_one_fifth radius W.criticalScale
      (weightedCanonicalCriticalScale_pos W)
      (ten_mul_radius_le_fullCoefficientCriticalScale
        S active hactive hradius htenRadiusSixteen Y X)
  have hproxyHalf : criticalScaleProxyRadius radius W.criticalScale
      (weightedCanonicalCriticalScale_pos W) ≤ (2 : NNReal)⁻¹ :=
    hproxyFifth.trans (by
      exact_mod_cast
        (show (1 / 5 : Real) ≤ (2 : Real)⁻¹ by norm_num))
  refine ⟨hproxyFifth, hproxyHalf, ?_⟩
  intro i
  change (affineAxisProxyTube
    (criticalScaleProxyRadius radius W.criticalScale
      (weightedCanonicalCriticalScale_pos W))
    (weightedCanonicalCriticalScaleAffineEquiv S W)
    (S.family.tubes i.1)).carrier ⊆ Metric.closedBall (0 : Space) 1
  apply affineAxisProxyTube_carrier_subset_closedBall_one
    (radius := radius)
    (s := criticalScaleProxyRadius radius W.criticalScale
      (weightedCanonicalCriticalScale_pos W))
    (weightedCanonicalCriticalScaleAffineEquiv S W)
    (S.family.tubes i.1)
  · exact norm_fullCoefficientAffineEquiv_axis_base_le_quarter
      S active hactive hradius htenRadiusSixteen Y X hcontained i
  · exact norm_fullCoefficientAffineEquiv_axis_endpoint_le_quarter
      S active hactive hradius htenRadiusSixteen Y X hactiveSource hcontained i
  · exact hproxyFifth

#print axioms fullCoefficientActualMass_proxySupport

end
end Family8FullCoefficientActualMassProxySupportV10
