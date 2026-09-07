import Family8Grounding.Family8FullCoefficientActualMassCriticalScaleV5
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyAxisLengthV1
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyTransverseRadiusV2
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyChartV1
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyFamilyV3
import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import Mathlib.Tactic

/-!
# Proxy geometry for the ten-radius full-coefficient actual-mass critical scale, V3

The full max metric controls all four graph-coefficient gaps directly, so the
critical-scale affine normalization needs no common graph-c bucket.  This
module supplies the longitudinal, transverse, and final-axis chart facts for
the same actual-mass weighted datum.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FullCoefficientActualMassProxyGeometryV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleAbsAxisChartV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8WeightedCanonicalCriticalScaleProxyAxisLengthV1
open Family8WeightedCanonicalCriticalScaleProxyChartV1
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open Family8WeightedCanonicalCriticalScaleProxyTransverseRadiusV2
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

theorem fullCoefficient_criticalBall_subset_active
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    W.criticalBall ⊆ active := by
  dsimp only
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  intro i hi
  exact W.criticalBall_subset_family hi

theorem fullCoefficient_criticalBall_graphA_gap
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    {i : iota}
    (hi : i ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).criticalBall) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    |projectedTubeGraphA (S.family.tubes i) -
      projectedTubeGraphA (S.family.tubes W.criticalCenter)| ≤
        W.criticalScale := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  exact (graphA_gap_le_fullCoefficientDistance
    (S.family.tubes i) (S.family.tubes W.criticalCenter)).trans
      (W.criticalBall_distance_to_center hi)

theorem fullCoefficient_criticalBall_graphB_gap
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    {i : iota}
    (hi : i ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).criticalBall) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    |projectedTubeGraphB (S.family.tubes i) -
      projectedTubeGraphB (S.family.tubes W.criticalCenter)| ≤
        W.criticalScale := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  exact (graphB_gap_le_fullCoefficientDistance
    (S.family.tubes i) (S.family.tubes W.criticalCenter)).trans
      (W.criticalBall_distance_to_center hi)

theorem fullCoefficient_criticalBall_graphC_gap
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    {i : iota}
    (hi : i ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).criticalBall) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    |projectedTubeGraphC (S.family.tubes i) -
      projectedTubeGraphC (S.family.tubes W.criticalCenter)| ≤
        W.criticalScale := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  exact (graphC_gap_le_fullCoefficientDistance
    (S.family.tubes i) (S.family.tubes W.criticalCenter)).trans
      (W.criticalBall_distance_to_center hi)

theorem fullCoefficient_criticalBall_graphD_gap
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    {i : iota}
    (hi : i ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).criticalBall) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    |projectedTubeGraphD (S.family.tubes i) -
      projectedTubeGraphD (S.family.tubes W.criticalCenter)| ≤
        W.criticalScale := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  exact (graphD_gap_le_fullCoefficientDistance
    (S.family.tubes i) (S.family.tubes W.criticalCenter)).trans
      (W.criticalBall_distance_to_center hi)

/-- The same full-metric datum supplies every geometric field of the round
critical-scale proxy. -/
theorem exists_fullCoefficientActualMass_proxyGeometry
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (hactiveSource : active ⊆ S.source) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    ∃ (_haxis : ∀ i : {i // i ∈ W.criticalBall},
        ‖affineImageAxisVector
          (weightedCanonicalCriticalScaleAffineEquiv S W)
          (S.family.tubes i.1)‖ ≤ 1)
      (_htransverse :
        affineLinearOperatorNorm
            (weightedCanonicalCriticalScaleAffineEquiv S W) *
              (radius : Real) ≤
          (criticalScaleProxyRadius radius W.criticalScale
            (weightedCanonicalCriticalScale_pos W) : Real)),
      ∀ i : {i // i ∈ W.criticalBall},
        (1 / 2 : Real) ≤
          |((weightedCanonicalCriticalScaleProxyFamily S W).tubes i).axis.direction 2| := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  have hballSource : ∀ i, i ∈ W.criticalBall → i ∈ S.source := by
    intro i hi
    apply hactiveSource
    exact W.criticalBall_subset_family hi
  have haxis : ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)‖ ≤ 1 := by
    intro i
    let t := W.criticalScale
    let T0 := S.family.tubes W.criticalCenter
    have ht : 0 < t := weightedCanonicalCriticalScale_pos W
    have hiVertical : (S.family.tubes i.1).axis.direction 2 ≠ 0 :=
      abs_pos.mp (by
        have := S.source_direction_final_half i.1 (hballSource i.1 i.2)
        linarith)
    change ‖affineImageAxisVector
      (criticalScaleAffineEquiv t ht
        (projectedTubeGraphA T0) (projectedTubeGraphB T0)
        (projectedTubeGraphC T0) (projectedTubeGraphD T0))
      (S.family.tubes i.1)‖ ≤ 1
    exact criticalScale_axisLength_le_one_of_graph_gaps_abs
      t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)
      (S.family.tubes i.1) hiVertical
      (fullCoefficient_criticalBall_graphC_gap S active hactive hradius
        htenRadiusSixteen Y X i.2)
      (fullCoefficient_criticalBall_graphD_gap S active hactive hradius
        htenRadiusSixteen Y X i.2)
  have htransverse := weightedCanonicalCriticalScaleProxy_transverseRadius
    S W (hballSource W.criticalCenter W.criticalCenter_mem_criticalBall)
      (by exact le_rfl)
  refine ⟨haxis, htransverse, ?_⟩
  intro i
  let t := W.criticalScale
  let T0 := S.family.tubes W.criticalCenter
  have ht : 0 < t := weightedCanonicalCriticalScale_pos W
  have hiVertical : (S.family.tubes i.1).axis.direction 2 ≠ 0 :=
    abs_pos.mp (by
      have := S.source_direction_final_half i.1 (hballSource i.1 i.2)
      linarith)
  change (1 / 2 : Real) ≤
    |(affineImageUnitExtensionAxis
      (criticalScaleAffineEquiv t ht
        (projectedTubeGraphA T0) (projectedTubeGraphB T0)
        (projectedTubeGraphC T0) (projectedTubeGraphD T0))
      (S.family.tubes i.1)).direction 2|
  exact criticalScale_axisDirection_final_half_of_graph_gaps_abs
    t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0)
    (S.family.tubes i.1) hiVertical
    (fullCoefficient_criticalBall_graphC_gap S active hactive hradius
      htenRadiusSixteen Y X i.2)
    (fullCoefficient_criticalBall_graphD_gap S active hactive hradius
      htenRadiusSixteen Y X i.2)

#print axioms fullCoefficient_criticalBall_subset_active
#print axioms fullCoefficient_criticalBall_graphA_gap
#print axioms fullCoefficient_criticalBall_graphB_gap
#print axioms fullCoefficient_criticalBall_graphC_gap
#print axioms fullCoefficient_criticalBall_graphD_gap
#print axioms exists_fullCoefficientActualMass_proxyGeometry

end
end Family8FullCoefficientActualMassProxyGeometryV7
