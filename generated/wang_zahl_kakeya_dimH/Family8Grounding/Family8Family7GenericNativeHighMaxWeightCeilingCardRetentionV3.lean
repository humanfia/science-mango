import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightCardRatioV1
import Family8Grounding.Family8Family7GenericNativeHighActivePatternMaxWeightFiberSubsetV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleAbsAxisChartV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighMaxWeightCeilingCardRetentionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Family7GenericNativeHighActivePatternMaxWeightCardRatioV1
open Family8Family7GenericNativeHighActivePatternMaxWeightFiberDefinitionV1
open Family8Family7GenericNativeHighActivePatternMaxWeightFiberSubsetV1
open Family8Family7GenericNativeHighActivePatternMaxWeightNormDataV1
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8Family7NativeHighCriticalScaleAbsAxisChartV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# The max-weight source family is the ceiling ball

Unit-ball support and the `L₃` direction chart bound every reduced graph
coefficient: `|A|,|B|≤3`, `|D|≤2`. Hence the reduced coefficient distance
between any two source tubes is at most `6+6+4=16`, exactly the canonical
ceiling. V1 omitted namespace openings; V2 left two definitional copies of
the norm datum unreconciled. Neither predecessor is imported.
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

theorem abs_projectedTubeGraphA_le_three_of_supported_vertical
    {radius : NNReal} (T : Tube radius)
    (hvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|)
    (hbase : T.axis.base ∈ Metric.closedBall (0 : Space) 1) :
    |projectedTubeGraphA T| ≤ 3 := by
  have hC := abs_projectedTubeGraphC_le_two_of_abs_final_half T hvertical
  have h0 := abs_coordinate_le_one_of_mem_closedBall_one T.axis.base hbase 0
  have h2 := abs_coordinate_le_one_of_mem_closedBall_one T.axis.base hbase 2
  unfold projectedTubeGraphA
  calc
    |T.axis.base 0 - projectedTubeGraphC T * T.axis.base 2| ≤
        |T.axis.base 0| + |projectedTubeGraphC T * T.axis.base 2| := abs_sub _ _
    _ = |T.axis.base 0| + |projectedTubeGraphC T| * |T.axis.base 2| := by
      rw [abs_mul]
    _ ≤ 1 + 2 * 1 := by gcongr
    _ = 3 := by norm_num

theorem abs_projectedTubeGraphB_le_three_of_supported_vertical
    {radius : NNReal} (T : Tube radius)
    (hvertical : (1 / 2 : Real) ≤ |T.axis.direction 2|)
    (hbase : T.axis.base ∈ Metric.closedBall (0 : Space) 1) :
    |projectedTubeGraphB T| ≤ 3 := by
  have hD := abs_projectedTubeGraphD_le_two_of_abs_final_half T hvertical
  have h1 := abs_coordinate_le_one_of_mem_closedBall_one T.axis.base hbase 1
  have h2 := abs_coordinate_le_one_of_mem_closedBall_one T.axis.base hbase 2
  unfold projectedTubeGraphB
  calc
    |T.axis.base 1 - projectedTubeGraphD T * T.axis.base 2| ≤
        |T.axis.base 1| + |projectedTubeGraphD T * T.axis.base 2| := abs_sub _ _
    _ = |T.axis.base 1| + |projectedTubeGraphD T| * |T.axis.base 2| := by
      rw [abs_mul]
    _ ≤ 1 + 2 * 1 := by gcongr
    _ = 3 := by norm_num

theorem projectedTubePairCoefficientDistance_le_sixteen_of_supported_vertical
    {radius : NNReal} (T U : Tube radius)
    (hverticalT : (1 / 2 : Real) ≤ |T.axis.direction 2|)
    (hverticalU : (1 / 2 : Real) ≤ |U.axis.direction 2|)
    (hbaseT : T.axis.base ∈ Metric.closedBall (0 : Space) 1)
    (hbaseU : U.axis.base ∈ Metric.closedBall (0 : Space) 1) :
    projectedTubePairCoefficientDistance T U ≤ 16 := by
  have hAT := abs_projectedTubeGraphA_le_three_of_supported_vertical
    T hverticalT hbaseT
  have hAU := abs_projectedTubeGraphA_le_three_of_supported_vertical
    U hverticalU hbaseU
  have hBT := abs_projectedTubeGraphB_le_three_of_supported_vertical
    T hverticalT hbaseT
  have hBU := abs_projectedTubeGraphB_le_three_of_supported_vertical
    U hverticalU hbaseU
  have hDT := abs_projectedTubeGraphD_le_two_of_abs_final_half T hverticalT
  have hDU := abs_projectedTubeGraphD_le_two_of_abs_final_half U hverticalU
  have hA : |projectedTubeGraphA T - projectedTubeGraphA U| ≤ 6 := by
    calc
      |projectedTubeGraphA T - projectedTubeGraphA U| ≤
          |projectedTubeGraphA T| + |projectedTubeGraphA U| := abs_sub _ _
      _ ≤ 6 := by linarith
  have hB : |projectedTubeGraphB T - projectedTubeGraphB U| ≤ 6 := by
    calc
      |projectedTubeGraphB T - projectedTubeGraphB U| ≤
          |projectedTubeGraphB T| + |projectedTubeGraphB U| := abs_sub _ _
      _ ≤ 6 := by linarith
  have hD : |projectedTubeGraphD T - projectedTubeGraphD U| ≤ 4 := by
    calc
      |projectedTubeGraphD T - projectedTubeGraphD U| ≤
          |projectedTubeGraphD T| + |projectedTubeGraphD U| := abs_sub _ _
      _ ≤ 4 := by linarith
  unfold projectedTubePairCoefficientDistance coefficientDistance
    projectedTubePairDeltaA projectedTubePairDeltaB projectedTubePairDeltaD
  linarith

theorem genericNativeHighActivePatternMaxWeight_family_subset_physicalAmbient
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0) :
    (genericNativeHighActivePatternMaxWeightNormData D G c hsource).family ⊆
      physical.ambient := by
  intro i hi
  have hiSelected : i ∈ genericNativeHighActivePatternMaxWeightFiber D G c := hi
  have hiFamily : i ∈
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).family :=
    genericNativeHighActivePatternMaxWeightFiber_subset D G c hiSelected
  rw [positiveCenterHighPayloadGlobalNormData_family] at hiFamily
  exact (mem_actualGlobalNormIndexFamily_iff S.family physical
    D.globalScale c.1.1).mp hiFamily |>.1

theorem genericNativeHighActivePatternMaxWeight_family_distance_le_ceiling
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0)
    (hambientSource : physical.ambient ⊆ S.source)
    (hcontained : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {i j : iota}
    (hi : i ∈ (genericNativeHighActivePatternMaxWeightNormData
      D G c hsource).family)
    (hj : j ∈ (genericNativeHighActivePatternMaxWeightNormData
      D G c hsource).family) :
    (genericNativeHighActivePatternMaxWeightNormData
      D G c hsource).distance i j ≤
    (genericNativeHighActivePatternMaxWeightNormData
      D G c hsource).ceiling := by
  let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
  have hiAmbient := genericNativeHighActivePatternMaxWeight_family_subset_physicalAmbient
    D G c hsource hi
  have hjAmbient := genericNativeHighActivePatternMaxWeight_family_subset_physicalAmbient
    D G c hsource hj
  have hiVertical := S.source_direction_final_half i (hambientSource hiAmbient)
  have hjVertical := S.source_direction_final_half j (hambientSource hjAmbient)
  have hiBase : (S.family.tubes i).axis.base ∈ Metric.closedBall (0 : Space) 1 :=
    hcontained i hiAmbient
      ((S.family.tubes i).axis_subset_carrier
        (S.family.tubes i).axis.base_mem_carrier)
  have hjBase : (S.family.tubes j).axis.base ∈ Metric.closedBall (0 : Space) 1 :=
    hcontained j hjAmbient
      ((S.family.tubes j).axis_subset_carrier
        (S.family.tubes j).axis.base_mem_carrier)
  change projectedTubePairCoefficientDistance
      (S.family.tubes i) (S.family.tubes j) ≤ 16
  exact projectedTubePairCoefficientDistance_le_sixteen_of_supported_vertical
    (S.family.tubes i) (S.family.tubes j) hiVertical hjVertical hiBase hjBase

theorem genericNativeHighActivePatternMaxWeight_ceilingBall_eq_family
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0)
    (hambientSource : physical.ambient ⊆ S.source)
    (hcontained : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
    W.family.filter (fun i ↦ W.distance i W.criticalCenter ≤ W.ceiling) =
      W.family := by
  let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact genericNativeHighActivePatternMaxWeight_family_distance_le_ceiling
    D G c hsource hambientSource hcontained hi W.criticalCenter_mem_family

theorem genericNativeHighActivePatternMaxWeight_familyCard_le_ceilingRatio
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsource : volume (genericNativeHighActivePatternSource D G c) ≠ 0)
    (hsourceTop : volume (genericNativeHighActivePatternSource D G c) ≠ ∞)
    (hambientSource : physical.ambient ⊆ S.source)
    (hcontained : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
    (W.family.card : ENNReal) ≤
      ((ENNReal.ofReal W.ceiling) / ENNReal.ofReal W.criticalScale) ^
          W.exponent * (W.criticalBall.card : ENNReal) := by
  let W := genericNativeHighActivePatternMaxWeightNormData D G c hsource
  have hcard := genericNativeHighActivePatternMaxWeight_ballCard_le
    D G c hsource hsourceTop W.delta_le_ceiling le_rfl
      W.criticalCenter W.criticalCenter_mem_family
  change (W.family.filter
      (fun i ↦ W.distance i W.criticalCenter ≤ W.ceiling)).card ≤
        ((ENNReal.ofReal W.ceiling) / ENNReal.ofReal W.criticalScale) ^
          W.exponent * (W.criticalBall.card : ENNReal) at hcard
  have hball := genericNativeHighActivePatternMaxWeight_ceilingBall_eq_family
    D G c hsource hambientSource hcontained
  change W.family.filter
      (fun i ↦ W.distance i W.criticalCenter ≤ W.ceiling) = W.family at hball
  rw [hball] at hcard
  exact hcard

end
end Family8Family7GenericNativeHighMaxWeightCeilingCardRetentionV3
