import Family8Grounding.Family8Family7NativeHighWeightedCriticalBallV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyDatumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1

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
# Critical-scale proxy for an arbitrary honest occurrence weight

The earlier proxy stack was definitionally tied to one particular first-hit
weight.  This successor bundles an arbitrary honest occurrence weight with
the native-high centre and geometry, then performs the same affine
normalization.  Scale, centre, subtype family, geometry, transported shading,
and final `ActualTubeDatum` all use that one bundled input.
-/

/-- Inputs which must stay definitionally synchronized throughout a weighted
critical-scale restart. -/
structure NativeHighArbitraryWeightedProxyInput
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) where
  geometry : NativeHighGeometry D
  center : D.HighCenter
  weight : iota → ENNReal

abbrev NativeHighArbitraryWeightedCriticalBallIndex
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D) :=
  {i // i ∈ (nativeHighWeightedNormData D P.center P.weight).criticalBall}

def nativeHighArbitraryWeightedCriticalBallFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D) :
    UniformTubeFamily radius
      (NativeHighArbitraryWeightedCriticalBallIndex D P) :=
  D.S.family.restrictTo
    (nativeHighWeightedNormData D P.center P.weight).criticalBall

@[simp] theorem nativeHighArbitraryWeightedCriticalBallFamily_tubes
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (i : NativeHighArbitraryWeightedCriticalBallIndex D P) :
    (nativeHighArbitraryWeightedCriticalBallFamily D P).tubes i =
      D.S.family.tubes i.1 :=
  rfl

/-- Literal source shading restricted to the same weighted ball. -/
def nativeHighArbitraryWeightedCriticalBallShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (Y : Shading D.S.family.bodyFamily) :
    Shading (nativeHighArbitraryWeightedCriticalBallFamily D P).bodyFamily where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

@[simp] theorem nativeHighArbitraryWeightedCriticalBallShading_carrier
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (Y : Shading D.S.family.bodyFamily)
    (i : NativeHighArbitraryWeightedCriticalBallIndex D P) :
    (nativeHighArbitraryWeightedCriticalBallShading D P Y).carrier i =
      Y.carrier i.1 :=
  rfl

theorem nativeHighArbitraryWeightedCriticalBallShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighArbitraryWeightedCriticalBallShading D P Y).shadingMass =
      ∑ i ∈ (nativeHighWeightedNormData D P.center P.weight).criticalBall,
        volume (Y.carrier i) := by
  unfold Shading.shadingMass
  simpa only [nativeHighArbitraryWeightedCriticalBallShading_carrier,
    Finset.univ_eq_attach] using
      Finset.sum_attach
        (nativeHighWeightedNormData D P.center P.weight).criticalBall
        (fun i => volume (Y.carrier i))

theorem nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D) :
    (nativeHighWeightedNormData D P.center P.weight).criticalBall ⊆
      D.physical.ambient := by
  exact nativeHighWeightedCriticalBall_subset_physicalAmbient
    D P.center P.weight

theorem nativeHighArbitraryWeightedCriticalScale_pos
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D) :
    0 < (nativeHighWeightedNormData D P.center P.weight).criticalScale :=
  (nativeHighWeightedNormData D P.center P.weight).delta_pos.trans_le
    (nativeHighWeightedNormData D P.center P.weight).criticalScale_bounds.1

def nativeHighArbitraryWeightedCriticalScaleAffineEquiv
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D) : Space ≃ᵃ[Real] Space :=
  let W := nativeHighWeightedNormData D P.center P.weight
  let T0 := D.S.family.tubes W.criticalCenter
  criticalScaleAffineEquiv W.criticalScale
    (nativeHighArbitraryWeightedCriticalScale_pos D P)
    (projectedTubeGraphA T0) (projectedTubeGraphB T0)
    (projectedTubeGraphC T0) (projectedTubeGraphD T0)

def nativeHighArbitraryWeightedCriticalScaleProxyFamily
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D) :
    UniformTubeFamily
      (criticalScaleProxyRadius radius
        (nativeHighWeightedNormData D P.center P.weight).criticalScale
        (nativeHighArbitraryWeightedCriticalScale_pos D P))
      (NativeHighArbitraryWeightedCriticalBallIndex D P) where
  tubes i := affineAxisProxyTube
    (criticalScaleProxyRadius radius
      (nativeHighWeightedNormData D P.center P.weight).criticalScale
      (nativeHighArbitraryWeightedCriticalScale_pos D P))
    (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)
    (D.S.family.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

structure NativeHighArbitraryWeightedCriticalScaleProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D) : Prop where
  axisLength : ∀ i : NativeHighArbitraryWeightedCriticalBallIndex D P,
    ‖affineImageAxisVector
      (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)
      (D.S.family.tubes i.1)‖ ≤ 1
  transverseRadius :
    affineLinearOperatorNorm
        (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) *
          (radius : Real) ≤
      (criticalScaleProxyRadius radius
        (nativeHighWeightedNormData D P.center P.weight).criticalScale
        (nativeHighArbitraryWeightedCriticalScale_pos D P) : Real)
  chart : ∀ i : NativeHighArbitraryWeightedCriticalBallIndex D P,
    (1 / 2 : Real) ≤
      |((nativeHighArbitraryWeightedCriticalScaleProxyFamily
        D P).tubes i).axis.direction 2|

/-- Producer-only construction of the weighted proxy geometry. -/
theorem nativeHighArbitraryWeightedCriticalScaleProxyGeometry
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source) :
    NativeHighArbitraryWeightedCriticalScaleProxyGeometry D P := by
  let W := nativeHighWeightedNormData D P.center P.weight
  let t := W.criticalScale
  let T0 := D.S.family.tubes W.criticalCenter
  have ht : 0 < t := nativeHighArbitraryWeightedCriticalScale_pos D P
  have hrefPhysical : W.criticalCenter ∈ D.physical.ambient :=
    nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient D P
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
      (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) ≤
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
      nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
        D P i.2
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
      · exact (P.geometry.hbucket i.1 hiAmbient).trans
          (P.geometry.hbucket W.criticalCenter hrefAmbient).symm
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
          (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) *
          (radius : Real) ≤ (2 / t) * (radius : Real) := by gcongr
      _ = 2 * (radius : Real) / t := by ring
  · intro i
    have hiAmbient : i.1 ∈ D.ambient :=
      nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
        D P i.2
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
      · exact (P.geometry.hbucket i.1 hiAmbient).trans
          (P.geometry.hbucket W.criticalCenter hrefAmbient).symm
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

def nativeHighArbitraryWeightedCriticalScaleProxyShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    Shading (nativeHighArbitraryWeightedCriticalScaleProxyFamily
      D P).bodyFamily where
  carrier i := nativeHighArbitraryWeightedCriticalScaleAffineEquiv D P ''
    Y.carrier i.1
  measurable_carrier i :=
    (nativeHighArbitraryWeightedCriticalScaleAffineEquiv
      D P).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i.1)
  carrier_subset i :=
    (Set.image_mono (Y.carrier_subset i.1)).trans
      (image_tubeCarrier_subset_affineAxisProxyTube
        (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)
        (D.S.family.tubes i.1)
        ((nativeHighArbitraryWeightedCriticalScaleProxyGeometry
          D P hambientSource).axisLength i)
        (nativeHighArbitraryWeightedCriticalScaleProxyGeometry
          D P hambientSource).transverseRadius)

theorem nativeHighArbitraryWeightedCriticalScaleProxyShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    (nativeHighArbitraryWeightedCriticalScaleProxyShading
      D P hambientSource Y).shadingMass =
      affineJacobian
        (nativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) *
      (nativeHighArbitraryWeightedCriticalBallShading D P Y).shadingMass := by
  unfold Shading.shadingMass
  simp_rw [nativeHighArbitraryWeightedCriticalScaleProxyShading,
    volume_image_affineEquiv]
  rw [Finset.mul_sum]
  simp only [nativeHighArbitraryWeightedCriticalBallShading_carrier]

def nativeHighArbitraryWeightedCriticalScaleProxyWZL3Source
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source) :
    WZL3UniformTubeSource
      (criticalScaleProxyRadius radius
        (nativeHighWeightedNormData D P.center P.weight).criticalScale
        (nativeHighArbitraryWeightedCriticalScale_pos D P))
      (NativeHighArbitraryWeightedCriticalBallIndex D P) where
  family := nativeHighArbitraryWeightedCriticalScaleProxyFamily D P
  source := Finset.univ
  source_direction_final_half := by
    intro i _hi
    exact (nativeHighArbitraryWeightedCriticalScaleProxyGeometry
      D P hambientSource).chart i

def nativeHighArbitraryWeightedCriticalScaleProxyDatum
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (P : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    ActualTubeDatum
      (criticalScaleProxyRadius radius
        (nativeHighWeightedNormData D P.center P.weight).criticalScale
        (nativeHighArbitraryWeightedCriticalScale_pos D P))
      (NativeHighArbitraryWeightedCriticalBallIndex D P) where
  family := nativeHighArbitraryWeightedCriticalScaleProxyFamily D P
  shading := nativeHighArbitraryWeightedCriticalScaleProxyShading
    D P hambientSource Y

#print axioms NativeHighArbitraryWeightedProxyInput
#print axioms nativeHighArbitraryWeightedCriticalBallFamily
#print axioms nativeHighArbitraryWeightedCriticalBallShading_shadingMass
#print axioms nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
#print axioms nativeHighArbitraryWeightedCriticalScale_pos
#print axioms nativeHighArbitraryWeightedCriticalScaleAffineEquiv
#print axioms nativeHighArbitraryWeightedCriticalScaleProxyGeometry
#print axioms nativeHighArbitraryWeightedCriticalScaleProxyShading
#print axioms nativeHighArbitraryWeightedCriticalScaleProxyShading_shadingMass
#print axioms nativeHighArbitraryWeightedCriticalScaleProxyWZL3Source
#print axioms nativeHighArbitraryWeightedCriticalScaleProxyDatum

end

end Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1
