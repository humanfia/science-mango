import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyFamilyV3
import Family8Grounding.Family8Family7NativeHighCriticalScaleAbsAxisChartV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open scoped NNReal

namespace Family8WeightedCanonicalCriticalScaleProxyAxisLengthV1

open LeanEval.Analysis.WangZahlKakeya
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleAbsAxisChartV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- The longitudinal proxy bound from literal critical-ball distance, a
half-radius graph-C gap, and source chart support. -/
theorem weightedCanonicalCriticalScaleProxy_axisLength
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (hsource : ∀ i, i ∈ W.criticalBall → i ∈ S.source)
    (hCgap : ∀ i, i ∈ W.criticalBall →
      |projectedTubeGraphC (S.family.tubes i) -
        projectedTubeGraphC (S.family.tubes W.criticalCenter)| ≤
          (radius : Real) / 2)
    (hdistance : ∀ i j,
      W.distance i j = projectedTubePairCoefficientDistance
        (S.family.tubes i) (S.family.tubes j))
    (hdelta : W.delta = (radius : Real)) :
    ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)‖ ≤ 1 := by
  intro i
  let t := W.criticalScale
  let T0 := S.family.tubes W.criticalCenter
  have ht : 0 < t := weightedCanonicalCriticalScale_pos W
  have hiForwardHalf :
      (1 / 2 : Real) ≤ |(S.family.tubes i.1).axis.direction 2| := by
    apply S.source_direction_final_half i.1
    exact hsource i.1 i.2
  have hiVertical : (S.family.tubes i.1).axis.direction 2 ≠ 0 :=
    abs_pos.mp (by linarith)
  have hscaleLower : (radius : Real) ≤ t := by
    rw [← hdelta]
    exact W.criticalScale_bounds.1
  have hC :
      |projectedTubeGraphC (S.family.tubes i.1) -
        projectedTubeGraphC T0| ≤ t := by
    exact (hCgap i.1 i.2).trans (by linarith)
  have hD :
      |projectedTubeGraphD (S.family.tubes i.1) -
        projectedTubeGraphD T0| ≤ t :=
    abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le (by
      have hd := W.criticalBall_distance_to_center i.2
      rw [hdistance] at hd
      exact hd)
  change ‖affineImageAxisVector
    (criticalScaleAffineEquiv t ht
      (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0))
    (S.family.tubes i.1)‖ ≤ 1
  exact criticalScale_axisLength_le_one_of_graph_gaps_abs
    t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0)
    (S.family.tubes i.1) hiVertical hC hD

end

end Family8WeightedCanonicalCriticalScaleProxyAxisLengthV1
