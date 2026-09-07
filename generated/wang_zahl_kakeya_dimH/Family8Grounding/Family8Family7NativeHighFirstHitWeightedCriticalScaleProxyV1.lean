import Family8Grounding.Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyDatumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighFirstHitWeightedCriticalScaleProxyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleAbsAxisChartV1
open Family8Family7NativeHighCriticalScaleAxisChartV1
open Family8Family7NativeHighCriticalScaleOperatorNormV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighFirstHitTubeOccurrenceNativeV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41ActualGlobalNormCoarseFiberV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# Critical-scale proxy for the actual first-hit weighted choice

The earlier proxy stack is definitionally tied to the cardinal-score
critical ball.  This additive successor performs the same honest affine
normalization on the mass-weighted critical choice produced from literal
first-hit tube occurrences.  Scale, centre, subtype family, geometry,
transported shading, and final `ActualTubeDatum` all use the same choice.
-/

abbrev NativeHighFirstHitWeightedCriticalBallIndex
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :=
  {i // i ∈ (nativeHighFirstHitWeightedNormData D G c).criticalBall}

def nativeHighFirstHitWeightedCriticalBallFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    UniformTubeFamily radius
      (NativeHighFirstHitWeightedCriticalBallIndex D G c) :=
  D.S.family.restrictTo
    (nativeHighFirstHitWeightedNormData D G c).criticalBall

@[simp] theorem nativeHighFirstHitWeightedCriticalBallFamily_tubes
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter)
    (i : NativeHighFirstHitWeightedCriticalBallIndex D G c) :
    (nativeHighFirstHitWeightedCriticalBallFamily D G c).tubes i =
      D.S.family.tubes i.1 :=
  rfl

/-- Literal source shading restricted to the same weighted ball. -/
def nativeHighFirstHitWeightedCriticalBallShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (Y : Shading D.S.family.bodyFamily) :
    Shading (nativeHighFirstHitWeightedCriticalBallFamily D G c).bodyFamily where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

@[simp] theorem nativeHighFirstHitWeightedCriticalBallShading_carrier
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (Y : Shading D.S.family.bodyFamily)
    (i : NativeHighFirstHitWeightedCriticalBallIndex D G c) :
    (nativeHighFirstHitWeightedCriticalBallShading D G c Y).carrier i =
      Y.carrier i.1 :=
  rfl

theorem nativeHighFirstHitWeightedCriticalBallShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (Y : Shading D.S.family.bodyFamily) :
    (nativeHighFirstHitWeightedCriticalBallShading D G c Y).shadingMass =
      ∑ i ∈ (nativeHighFirstHitWeightedNormData D G c).criticalBall,
        volume (Y.carrier i) := by
  unfold Shading.shadingMass
  simpa only [nativeHighFirstHitWeightedCriticalBallShading_carrier,
    Finset.univ_eq_attach] using
      Finset.sum_attach
        (nativeHighFirstHitWeightedNormData D G c).criticalBall
        (fun i => volume (Y.carrier i))

theorem nativeHighFirstHitWeightedCriticalBall_subset_physicalAmbient
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    (nativeHighFirstHitWeightedNormData D G c).criticalBall ⊆
      D.physical.ambient := by
  intro i hi
  have hiFamily :=
    (nativeHighFirstHitWeightedNormData D G c).criticalBall_subset_family hi
  change i ∈ (nativeHighFirstHitNormData D c).family at hiFamily
  unfold nativeHighFirstHitNormData at hiFamily
  rw [positiveCenterHighPayloadGlobalNormData_family] at hiFamily
  exact (mem_actualGlobalNormIndexFamily_iff D.S.family D.physical
    D.globalScale c.1.1).mp hiFamily |>.1

theorem nativeHighFirstHitWeightedCriticalScale_pos
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    0 < (nativeHighFirstHitWeightedNormData D G c).criticalScale :=
  (nativeHighFirstHitWeightedNormData D G c).delta_pos.trans_le
    (nativeHighFirstHitWeightedNormData D G c).criticalScale_bounds.1

def nativeHighFirstHitWeightedCriticalScaleAffineEquiv
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : Space ≃ᵃ[Real] Space :=
  let W := nativeHighFirstHitWeightedNormData D G c
  let T0 := D.S.family.tubes W.criticalCenter
  criticalScaleAffineEquiv W.criticalScale
    (nativeHighFirstHitWeightedCriticalScale_pos D G c)
    (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0)

def nativeHighFirstHitWeightedCriticalScaleProxyFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) :
    UniformTubeFamily
      (criticalScaleProxyRadius radius
        (nativeHighFirstHitWeightedNormData D G c).criticalScale
        (nativeHighFirstHitWeightedCriticalScale_pos D G c))
      (NativeHighFirstHitWeightedCriticalBallIndex D G c) where
  tubes i := affineAxisProxyTube
    (criticalScaleProxyRadius radius
      (nativeHighFirstHitWeightedNormData D G c).criticalScale
      (nativeHighFirstHitWeightedCriticalScale_pos D G c))
    (nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c)
    (D.S.family.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

structure NativeHighFirstHitWeightedCriticalScaleProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : Prop where
  axisLength : ∀ i : NativeHighFirstHitWeightedCriticalBallIndex D G c,
    ‖affineImageAxisVector
      (nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c)
      (D.S.family.tubes i.1)‖ ≤ 1
  transverseRadius :
    affineLinearOperatorNorm
        (nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c) *
          (radius : Real) ≤
      (criticalScaleProxyRadius radius
        (nativeHighFirstHitWeightedNormData D G c).criticalScale
        (nativeHighFirstHitWeightedCriticalScale_pos D G c) : Real)
  chart : ∀ i : NativeHighFirstHitWeightedCriticalBallIndex D G c,
    (1 / 2 : Real) ≤
      |((nativeHighFirstHitWeightedCriticalScaleProxyFamily D G c).tubes i).axis.direction 2|

/-- Producer-only construction of the weighted proxy geometry. -/
theorem nativeHighFirstHitWeightedCriticalScaleProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (hambientSource : D.ambient ⊆ D.S.source) :
    NativeHighFirstHitWeightedCriticalScaleProxyGeometry D G c := by
  let W := nativeHighFirstHitWeightedNormData D G c
  let t := W.criticalScale
  let T0 := D.S.family.tubes W.criticalCenter
  have ht : 0 < t := nativeHighFirstHitWeightedCriticalScale_pos D G c
  have hrefPhysical : W.criticalCenter ∈ D.physical.ambient :=
    nativeHighFirstHitWeightedCriticalBall_subset_physicalAmbient D G c
      W.criticalCenter_mem_criticalBall
  have hrefAmbient : W.criticalCenter ∈ D.ambient := hrefPhysical
  have hrefForwardHalf : (1 / 2 : Real) ≤ |T0.axis.direction 2| := by
    apply D.S.source_direction_final_half W.criticalCenter
    exact hambientSource hrefAmbient
  have hc0 : |projectedTubeGraphC T0| ≤ 2 :=
    abs_projectedTubeGraphC_le_two_of_abs_final_half T0 hrefForwardHalf
  have hd0 : |projectedTubeGraphD T0| ≤ 2 :=
    abs_projectedTubeGraphD_le_two_of_abs_final_half T0 hrefForwardHalf
  have hscaleUpper : t ≤ 16 := by
    have h := W.criticalScale_bounds.2
    change t ≤ 16
    exact h
  have hop : affineLinearOperatorNorm
      (nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c) ≤
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
    have hiAmbient : i.1 ∈ D.ambient :=
      nativeHighFirstHitWeightedCriticalBall_subset_physicalAmbient
        D G c i.2
    have hiForwardHalf :
        (1 / 2 : Real) ≤ |(D.S.family.tubes i.1).axis.direction 2| := by
      apply D.S.source_direction_final_half i.1
      exact hambientSource hiAmbient
    have hiVertical : (D.S.family.tubes i.1).axis.direction 2 ≠ 0 :=
      abs_pos.mp (by linarith)
    have hCsmall :
        |projectedTubeGraphC (D.S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ (radius : Real) / 2 := by
      apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
      · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
      · exact (G.hbucket i.1 hiAmbient).trans
          (G.hbucket W.criticalCenter hrefAmbient).symm
    have hscaleLower : (radius : Real) ≤ t := by
      have h := W.criticalScale_bounds.1
      change (radius : Real) ≤ t
      exact h
    have hC :
        |projectedTubeGraphC (D.S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ t :=
      hCsmall.trans (by linarith)
    have hD :
        |projectedTubeGraphD (D.S.family.tubes i.1) -
          projectedTubeGraphD T0| ≤ t :=
      abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le
        (by
          have hd := W.criticalBall_distance_to_center i.2
          change projectedTubePairCoefficientDistance
            (D.S.family.tubes i.1) T0 ≤ t at hd
          exact hd)
    change ‖affineImageAxisVector
      (criticalScaleAffineEquiv t ht
        (projectedTubeGraphA T0) (projectedTubeGraphB T0)
        (projectedTubeGraphC T0) (projectedTubeGraphD T0))
      (D.S.family.tubes i.1)‖ ≤ 1
    exact criticalScale_axisLength_le_one_of_graph_gaps_abs
      t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)
      (D.S.family.tubes i.1) hiVertical hC hD
  · rw [criticalScaleProxyRadius_coe]
    calc
      affineLinearOperatorNorm
          (nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c) *
          (radius : Real) ≤ (2 / t) * (radius : Real) := by gcongr
      _ = 2 * (radius : Real) / t := by ring
  · intro i
    have hiAmbient : i.1 ∈ D.ambient :=
      nativeHighFirstHitWeightedCriticalBall_subset_physicalAmbient
        D G c i.2
    have hiForwardHalf :
        (1 / 2 : Real) ≤ |(D.S.family.tubes i.1).axis.direction 2| := by
      apply D.S.source_direction_final_half i.1
      exact hambientSource hiAmbient
    have hiVertical : (D.S.family.tubes i.1).axis.direction 2 ≠ 0 :=
      abs_pos.mp (by linarith)
    have hCsmall :
        |projectedTubeGraphC (D.S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ (radius : Real) / 2 := by
      apply abs_projectedTubeGraphC_sub_le_of_bucket_eq
      · exact div_pos (by exact_mod_cast D.hradius) (by norm_num)
      · exact (G.hbucket i.1 hiAmbient).trans
          (G.hbucket W.criticalCenter hrefAmbient).symm
    have hscaleLower : (radius : Real) ≤ t := by
      have h := W.criticalScale_bounds.1
      change (radius : Real) ≤ t
      exact h
    have hC :
        |projectedTubeGraphC (D.S.family.tubes i.1) -
          projectedTubeGraphC T0| ≤ t :=
      hCsmall.trans (by linarith)
    have hD :
        |projectedTubeGraphD (D.S.family.tubes i.1) -
          projectedTubeGraphD T0| ≤ t :=
      abs_projectedTubeGraphD_sub_le_of_pairCoefficientDistance_le
        (by
          have hd := W.criticalBall_distance_to_center i.2
          change projectedTubePairCoefficientDistance
            (D.S.family.tubes i.1) T0 ≤ t at hd
          exact hd)
    change (1 / 2 : Real) ≤
      |(affineImageUnitExtensionAxis
        (criticalScaleAffineEquiv t ht
          (projectedTubeGraphA T0) (projectedTubeGraphB T0)
          (projectedTubeGraphC T0) (projectedTubeGraphD T0))
        (D.S.family.tubes i.1)).direction 2|
    exact criticalScale_axisDirection_final_half_of_graph_gaps_abs
      t ht (projectedTubeGraphA T0) (projectedTubeGraphB T0)
      (projectedTubeGraphC T0) (projectedTubeGraphD T0)
      (D.S.family.tubes i.1) hiVertical hC hD

def nativeHighFirstHitWeightedCriticalScaleProxyShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    Shading (nativeHighFirstHitWeightedCriticalScaleProxyFamily D G c).bodyFamily where
  carrier i := nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c ''
    Y.carrier i.1
  measurable_carrier i :=
    (nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i.1)
  carrier_subset i :=
    (Set.image_mono (Y.carrier_subset i.1)).trans
      (image_tubeCarrier_subset_affineAxisProxyTube
        (nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c)
        (D.S.family.tubes i.1)
        ((nativeHighFirstHitWeightedCriticalScaleProxyGeometry
          D G c hambientSource).axisLength i)
        (nativeHighFirstHitWeightedCriticalScaleProxyGeometry
          D G c hambientSource).transverseRadius)

theorem nativeHighFirstHitWeightedCriticalScaleProxyShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighFirstHitWeightedCriticalScaleProxyShading
      D G c hambientSource Y).shadingMass =
      affineJacobian
        (nativeHighFirstHitWeightedCriticalScaleAffineEquiv D G c) *
      (nativeHighFirstHitWeightedCriticalBallShading D G c Y).shadingMass := by
  unfold Shading.shadingMass
  simp_rw [nativeHighFirstHitWeightedCriticalScaleProxyShading,
    volume_image_affineEquiv]
  rw [Finset.mul_sum]
  simp only [nativeHighFirstHitWeightedCriticalBallShading_carrier]

def nativeHighFirstHitWeightedCriticalScaleProxyWZL3Source
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (hambientSource : D.ambient ⊆ D.S.source) :
    WZL3UniformTubeSource
      (criticalScaleProxyRadius radius
        (nativeHighFirstHitWeightedNormData D G c).criticalScale
        (nativeHighFirstHitWeightedCriticalScale_pos D G c))
      (NativeHighFirstHitWeightedCriticalBallIndex D G c) where
  family := nativeHighFirstHitWeightedCriticalScaleProxyFamily D G c
  source := Finset.univ
  source_direction_final_half := by
    intro i _hi
    exact (nativeHighFirstHitWeightedCriticalScaleProxyGeometry
      D G c hambientSource).chart i

def nativeHighFirstHitWeightedCriticalScaleProxyDatum
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    ActualTubeDatum
      (criticalScaleProxyRadius radius
        (nativeHighFirstHitWeightedNormData D G c).criticalScale
        (nativeHighFirstHitWeightedCriticalScale_pos D G c))
      (NativeHighFirstHitWeightedCriticalBallIndex D G c) where
  family := nativeHighFirstHitWeightedCriticalScaleProxyFamily D G c
  shading := nativeHighFirstHitWeightedCriticalScaleProxyShading
    D G c hambientSource Y

#print axioms nativeHighFirstHitWeightedCriticalBallFamily
#print axioms nativeHighFirstHitWeightedCriticalBallShading_shadingMass
#print axioms nativeHighFirstHitWeightedCriticalBall_subset_physicalAmbient
#print axioms nativeHighFirstHitWeightedCriticalScale_pos
#print axioms nativeHighFirstHitWeightedCriticalScaleAffineEquiv
#print axioms nativeHighFirstHitWeightedCriticalScaleProxyGeometry
#print axioms nativeHighFirstHitWeightedCriticalScaleProxyShading
#print axioms nativeHighFirstHitWeightedCriticalScaleProxyShading_shadingMass
#print axioms nativeHighFirstHitWeightedCriticalScaleProxyWZL3Source
#print axioms nativeHighFirstHitWeightedCriticalScaleProxyDatum

end

end Family8Family7NativeHighFirstHitWeightedCriticalScaleProxyV1
