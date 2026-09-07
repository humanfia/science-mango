import Family8Grounding.Family8Family7NativeHighCriticalScaleOperatorNormV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleAbsAxisChartV1
import Family8Grounding.Family8Family7NativeHighNearSaturatedNormSplitV1
import FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleProxyGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighCriticalBallDatumV1
open Family8Family7NativeHighCriticalBallAffineProxyV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleAxisChartV1
open Family8Family7NativeHighCriticalScaleAbsAxisChartV1
open Family8Family7NativeHighCriticalScaleOperatorNormV1
open Family8Family7NativeHighNearSaturatedNormSplitV1
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentPlankFineProxyCarrierV3
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32FiniteNormCriticalBallV1
open FamilyStickyCinematicL32ContinuumActualCriticalScaleMapV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u

/-!
# Concrete critical-scale proxy geometry

The canonical critical scale supplies the missing transverse normalization.
The native common `C` bucket controls the graph-`C` gap, while the literal
canonical metric controls the graph-`D` gap.  Together with the inherited
`L_3` chart, these facts instantiate the affine proxy geometry with radius
`2 * radius / criticalScale`, without a conclusion-valued callback.
-/

/-- The natural round-tube radius after the concrete critical-scale map. -/
def criticalScaleProxyRadius (radius : NNReal) (t : Real) (ht : 0 < t) :
    NNReal :=
  ⟨2 * (radius : Real) / t, by positivity⟩

@[simp] theorem criticalScaleProxyRadius_coe
    (radius : NNReal) (t : Real) (ht : 0 < t) :
    (criticalScaleProxyRadius radius t ht : Real) =
      2 * (radius : Real) / t :=
  rfl

/-- Positivity of the literal canonical critical scale. -/
theorem nativeHighCriticalScale_pos
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    0 < (positiveCenterHighPayloadGlobalNormData
      (D.chosenHighPayloadAt c)).criticalScale := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  exact N.delta_pos.trans_le
    (finiteCriticalMaximizerScale_bounds N.family N.distance
      N.family_nonempty N.delta_le_ceiling).1

/-- Concrete normalization centered at the canonical critical tube. -/
def nativeHighCriticalScaleAffineEquiv
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter) :
    Space ≃ᵃ[Real] Space :=
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  let T0 := D.S.family.tubes N.criticalCenter
  criticalScaleAffineEquiv N.criticalScale
    (nativeHighCriticalScale_pos D c)
    (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0)

/-- The graph-`D` component is bounded by the reduced coefficient metric. -/
theorem abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le
    {radius : NNReal} {T U : Tube radius} {t : Real}
    (hTU : projectedTubePairCoefficientDistance T U ≤ t) :
    |projectedTubeGraphD T - projectedTubeGraphD U| ≤ t := by
  unfold projectedTubePairCoefficientDistance coefficientDistance
    projectedTubePairDeltaA projectedTubePairDeltaB projectedTubePairDeltaD
    at hTU
  nlinarith [abs_nonneg
    (projectedTubeGraphA T - projectedTubeGraphA U),
    abs_nonneg (projectedTubeGraphB T - projectedTubeGraphB U)]

/-- Tenfold scale separation makes the normalized proxy radius at most
`1/5`; this is the genuine scale gain on the critical-ball-rich branch. -/
theorem criticalScaleProxyRadius_le_one_fifth
    (radius : NNReal) (t : Real) (ht : 0 < t)
    (hten : 10 * (radius : Real) ≤ t) :
    criticalScaleProxyRadius radius t ht ≤ (1 / 5 : NNReal) := by
  apply NNReal.coe_le_coe.mp
  simp only [criticalScaleProxyRadius_coe, NNReal.coe_div, NNReal.coe_one]
  apply (div_le_iff₀ ht).2
  calc
    2 * (radius : Real) ≤ t / 5 := by nlinarith
    _ = (1 / 5 : Real) * t := by ring

/-- The actual native critical ball has a concrete affine proxy geometry.
Every field is derived from producer data: no rescaling callback occurs. -/
theorem nativeHighCriticalScaleAffineProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source) :
    NativeHighCriticalBallAffineProxyGeometry
      (criticalScaleProxyRadius radius
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalScale
        (nativeHighCriticalScale_pos D c))
      (nativeHighCriticalScaleAffineEquiv D c) D c := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  let t := N.criticalScale
  let T0 := D.S.family.tubes N.criticalCenter
  have ht : 0 < t := by
    simpa only [N, t] using nativeHighCriticalScale_pos D c
  have hrefPhysical : N.criticalCenter ∈ D.physical.ambient := by
    exact datum.subset_physicalAmbient datum.center_mem
  have hrefAmbient : N.criticalCenter ∈ D.ambient := hrefPhysical
  have hrefForwardHalf :
      (1 / 2 : Real) ≤ |T0.axis.direction 2| := by
    apply D.S.source_direction_final_half N.criticalCenter
    exact hambientSource hrefAmbient
  have hc0 : |projectedTubeGraphC T0| ≤ 2 :=
    abs_projectedTubeGraphC_le_two_of_abs_final_half T0 hrefForwardHalf
  have hd0 : |projectedTubeGraphD T0| ≤ 2 :=
    abs_projectedTubeGraphD_le_two_of_abs_final_half T0 hrefForwardHalf
  have hop : affineLinearOperatorNorm
      (nativeHighCriticalScaleAffineEquiv D c) ≤ 2 / t := by
    change affineLinearOperatorNorm
      (criticalScaleAffineEquiv t (nativeHighCriticalScale_pos D c)
        (projectedTubeGraphA T0) (projectedTubeGraphB T0)
        (projectedTubeGraphC T0) (projectedTubeGraphD T0)) ≤ 2 / t
    exact affineLinearOperatorNorm_criticalScaleAffineEquiv_le_two_div
      t (nativeHighCriticalScale_pos D c)
      (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)
      datum.scale_bounds.2 hc0 hd0
  refine {
    axisLength := ?_
    transverseRadius := ?_
    chart := ?_ }
  · intro i
    have hiAmbient : i.1 ∈ D.ambient := datum.subset_physicalAmbient i.2
    have hiForwardHalf :
        (1 / 2 : Real) ≤ |(D.S.family.tubes i.1).axis.direction 2| := by
      apply D.S.source_direction_final_half i.1
      exact hambientSource hiAmbient
    have hiVertical : (D.S.family.tubes i.1).axis.direction 2 ≠ 0 := by
      exact abs_pos.mp (by linarith)
    have hCsmall :
        |projectedTubeGraphC (D.S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ (radius : Real) / 2 := by
      apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
      · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
      · exact (G.hbucket i.1 hiAmbient).trans
          (G.hbucket N.criticalCenter hrefAmbient).symm
    have hC :
        |projectedTubeGraphC (D.S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ t := by
      exact hCsmall.trans (by
        have := datum.scale_bounds.1
        change (radius : Real) ≤ t at this
        linarith)
    have hdistance := datum.distance_to_center i.1 i.2
    change projectedTubePairCoefficientDistance
      (D.S.family.tubes i.1) T0 ≤ t at hdistance
    have hD :
        |projectedTubeGraphD (D.S.family.tubes i.1) -
          projectedTubeGraphD T0| ≤ t :=
      abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le hdistance
    change ‖affineImageAxisVector
      (criticalScaleAffineEquiv t (nativeHighCriticalScale_pos D c)
        (projectedTubeGraphA T0) (projectedTubeGraphB T0)
        (projectedTubeGraphC T0) (projectedTubeGraphD T0))
      (D.S.family.tubes i.1)‖ ≤ 1
    exact criticalScale_axisLength_le_one_of_graph_gaps_abs
      t (nativeHighCriticalScale_pos D c)
      (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)
      (D.S.family.tubes i.1) hiVertical hC hD
  · rw [criticalScaleProxyRadius_coe]
    calc
      affineLinearOperatorNorm (nativeHighCriticalScaleAffineEquiv D c) *
          (radius : Real) ≤ (2 / t) * (radius : Real) := by
        gcongr
      _ = 2 * (radius : Real) / t := by ring
  · intro i
    have hiAmbient : i.1 ∈ D.ambient := datum.subset_physicalAmbient i.2
    have hiForwardHalf :
        (1 / 2 : Real) ≤ |(D.S.family.tubes i.1).axis.direction 2| := by
      apply D.S.source_direction_final_half i.1
      exact hambientSource hiAmbient
    have hiVertical : (D.S.family.tubes i.1).axis.direction 2 ≠ 0 := by
      exact abs_pos.mp (by linarith)
    have hCsmall :
        |projectedTubeGraphC (D.S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ (radius : Real) / 2 := by
      apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
      · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
      · exact (G.hbucket i.1 hiAmbient).trans
          (G.hbucket N.criticalCenter hrefAmbient).symm
    have hC :
        |projectedTubeGraphC (D.S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ t := by
      exact hCsmall.trans (by
        have := datum.scale_bounds.1
        change (radius : Real) ≤ t at this
        linarith)
    have hdistance := datum.distance_to_center i.1 i.2
    change projectedTubePairCoefficientDistance
      (D.S.family.tubes i.1) T0 ≤ t at hdistance
    have hD :
        |projectedTubeGraphD (D.S.family.tubes i.1) -
          projectedTubeGraphD T0| ≤ t :=
      abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le hdistance
    change (1 / 2 : Real) ≤
      |(affineImageUnitExtensionAxis
        (criticalScaleAffineEquiv t (nativeHighCriticalScale_pos D c)
          (projectedTubeGraphA T0) (projectedTubeGraphB T0)
          (projectedTubeGraphC T0) (projectedTubeGraphD T0))
        (D.S.family.tubes i.1)).direction 2|
    exact criticalScale_axisDirection_final_half_of_graph_gaps_abs
      t (nativeHighCriticalScale_pos D c)
      (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)
      (D.S.family.tubes i.1) hiVertical hC hD

/-- On a rich centre, the concrete proxy radius is at most `1/5`. -/
theorem nativeHighCriticalScaleProxyRadius_le_one_fifth_of_richCenter
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter}
    (hc : c ∈ nativeHighNearSaturatedCriticalBallRichCenters D G) :
    criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c) ≤ (1 / 5 : NNReal) := by
  let N := positiveCenterHighPayloadGlobalNormData (D.chosenHighPayloadAt c)
  have hcData := Finset.mem_filter.mp hc
  have htenBall : 10 * G.ballRadius c ≤ N.criticalScale := by
    simpa only [N] using le_of_not_gt hcData.2
  have htenRadius : 10 * (radius : Real) ≤ N.criticalScale := by
    have hradiusBall : (radius : Real) ≤ G.ballRadius c := by
      simpa [N, positiveCenterHighPayloadGlobalNormData,
        actualGlobalNormIndexData] using G.hballRadiusLower c
    nlinarith
  exact criticalScaleProxyRadius_le_one_fifth radius N.criticalScale
    (nativeHighCriticalScale_pos D c) htenRadius

#print axioms criticalScaleProxyRadius
#print axioms nativeHighCriticalScale_pos
#print axioms nativeHighCriticalScaleAffineEquiv
#print axioms abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le
#print axioms criticalScaleProxyRadius_le_one_fifth
#print axioms nativeHighCriticalScaleAffineProxyGeometry
#print axioms nativeHighCriticalScaleProxyRadius_le_one_fifth_of_richCenter

end

end Family8Family7NativeHighCriticalScaleProxyGeometryV1
