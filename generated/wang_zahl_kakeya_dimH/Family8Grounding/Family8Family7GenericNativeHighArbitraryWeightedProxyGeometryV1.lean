import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7GenericNativeHighArbitraryWeightedProxyGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighCriticalScaleAbsAxisChartV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleOperatorNormV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

structure GenericNativeHighArbitraryWeightedCriticalScaleProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D) : Prop where
  axisLength :
    ∀ i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P,
      ‖affineImageAxisVector
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)
        (S.family.tubes i.1)‖ ≤ 1
  transverseRadius :
    affineLinearOperatorNorm
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) *
          (radius : Real) ≤
      (criticalScaleProxyRadius radius
        (genericNativeHighWeightedNormData D P.center P.weight).criticalScale
        (genericNativeHighArbitraryWeightedCriticalScale_pos D P) : Real)
  chart :
    ∀ i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P,
      (1 / 2 : Real) ≤
        |((genericNativeHighArbitraryWeightedCriticalScaleProxyFamily
          D P).tubes i).axis.direction 2|

theorem genericNativeHighArbitraryWeightedCriticalScaleProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source) :
    GenericNativeHighArbitraryWeightedCriticalScaleProxyGeometry D P := by
  let W := genericNativeHighWeightedNormData D P.center P.weight
  let t := W.criticalScale
  let T0 := S.family.tubes W.criticalCenter
  have ht : 0 < t :=
    genericNativeHighArbitraryWeightedCriticalScale_pos D P
  have hrefAmbient : W.criticalCenter ∈ physical.ambient :=
    genericNativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
      D P W.criticalCenter_mem_criticalBall
  have hrefForwardHalf : (1 / 2 : Real) ≤ |T0.axis.direction 2| := by
    apply S.source_direction_final_half W.criticalCenter
    exact hambientSource hrefAmbient
  have hc0 : |projectedTubeGraphC T0| ≤ 2 :=
    abs_projectedTubeGraphC_le_two_of_abs_final_half T0 hrefForwardHalf
  have hd0 : |projectedTubeGraphD T0| ≤ 2 :=
    abs_projectedTubeGraphD_le_two_of_abs_final_half T0 hrefForwardHalf
  have hscaleUpper : t ≤ 16 := by
    have h := W.criticalScale_bounds.2
    change t ≤ 16
    exact h
  have hop :
      affineLinearOperatorNorm
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) ≤
          2 / t := by
    change affineLinearOperatorNorm
      (criticalScaleAffineEquiv t ht
        (projectedTubeGraphA T0) (projectedTubeGraphB T0)
        (projectedTubeGraphC T0) (projectedTubeGraphD T0)) ≤ 2 / t
    exact affineLinearOperatorNorm_criticalScaleAffineEquiv_le_two_div
      t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)
      hscaleUpper hc0 hd0
  refine { axisLength := ?_, transverseRadius := ?_, chart := ?_ }
  · intro i
    have hiAmbient : i.1 ∈ physical.ambient :=
      genericNativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
        D P i.2
    have hiForwardHalf :
        (1 / 2 : Real) ≤ |(S.family.tubes i.1).axis.direction 2| := by
      apply S.source_direction_final_half i.1
      exact hambientSource hiAmbient
    have hiVertical : (S.family.tubes i.1).axis.direction 2 ≠ 0 :=
      abs_pos.mp (by linarith)
    have hCsmall :
        |projectedTubeGraphC (S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ (radius : Real) / 2 := by
      apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
      · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
      · exact (P.geometry.hbucket i.1 hiAmbient).trans
          (P.geometry.hbucket W.criticalCenter hrefAmbient).symm
    have hscaleLower : (radius : Real) ≤ t := by
      have h := W.criticalScale_bounds.1
      change (radius : Real) ≤ t
      exact h
    have hC :
        |projectedTubeGraphC (S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ t :=
      hCsmall.trans (by linarith)
    have hD :
        |projectedTubeGraphD (S.family.tubes i.1) -
          projectedTubeGraphD T0| ≤ t :=
      abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le
        (by
          have hd := W.criticalBall_distance_to_center i.2
          change projectedTubePairCoefficientDistance
            (S.family.tubes i.1) T0 ≤ t at hd
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
  · rw [criticalScaleProxyRadius_coe]
    calc
      affineLinearOperatorNorm
          (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) *
          (radius : Real) ≤ (2 / t) * (radius : Real) := by
        gcongr
      _ = 2 * (radius : Real) / t := by ring
  · intro i
    have hiAmbient : i.1 ∈ physical.ambient :=
      genericNativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
        D P i.2
    have hiForwardHalf :
        (1 / 2 : Real) ≤ |(S.family.tubes i.1).axis.direction 2| := by
      apply S.source_direction_final_half i.1
      exact hambientSource hiAmbient
    have hiVertical : (S.family.tubes i.1).axis.direction 2 ≠ 0 :=
      abs_pos.mp (by linarith)
    have hCsmall :
        |projectedTubeGraphC (S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ (radius : Real) / 2 := by
      apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
      · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
      · exact (P.geometry.hbucket i.1 hiAmbient).trans
          (P.geometry.hbucket W.criticalCenter hrefAmbient).symm
    have hscaleLower : (radius : Real) ≤ t := by
      have h := W.criticalScale_bounds.1
      change (radius : Real) ≤ t
      exact h
    have hC :
        |projectedTubeGraphC (S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ t :=
      hCsmall.trans (by linarith)
    have hD :
        |projectedTubeGraphD (S.family.tubes i.1) -
          projectedTubeGraphD T0| ≤ t :=
      abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le
        (by
          have hd := W.criticalBall_distance_to_center i.2
          change projectedTubePairCoefficientDistance
            (S.family.tubes i.1) T0 ≤ t at hd
          exact hd)
    change (1 / 2 : Real) ≤
      |(affineImageUnitExtensionAxis
        (criticalScaleAffineEquiv t ht
          (projectedTubeGraphA T0) (projectedTubeGraphB T0)
          (projectedTubeGraphC T0) (projectedTubeGraphD T0))
        (S.family.tubes i.1)).direction 2|
    exact criticalScale_axisDirection_final_half_of_graph_gaps_abs
      t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)
      (S.family.tubes i.1) hiVertical hC hD

#print axioms
  GenericNativeHighArbitraryWeightedCriticalScaleProxyGeometry
#print axioms
  genericNativeHighArbitraryWeightedCriticalScaleProxyGeometry

end

end Family8Family7GenericNativeHighArbitraryWeightedProxyGeometryV1
