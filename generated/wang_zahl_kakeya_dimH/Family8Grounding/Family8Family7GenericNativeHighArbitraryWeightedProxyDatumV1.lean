import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxyGeometryV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighArbitraryWeightedProxyDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyGeometryV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

def genericNativeHighArbitraryWeightedCriticalScaleProxyShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily) :
    Shading
      (genericNativeHighArbitraryWeightedCriticalScaleProxyFamily
        D P).bodyFamily where
  carrier i :=
    genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P ''
      Y.carrier i.1
  measurable_carrier i :=
    (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv
      D P).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i.1)
  carrier_subset i :=
    (Set.image_mono (Y.carrier_subset i.1)).trans
      (image_tubeCarrier_subset_affineAxisProxyTube
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)
        (S.family.tubes i.1)
        ((genericNativeHighArbitraryWeightedCriticalScaleProxyGeometry
          D P hambientSource).axisLength i)
        (genericNativeHighArbitraryWeightedCriticalScaleProxyGeometry
          D P hambientSource).transverseRadius)

@[simp] theorem
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_carrier
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily)
    (i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P) :
    (genericNativeHighArbitraryWeightedCriticalScaleProxyShading
      D P hambientSource Y).carrier i =
      genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P ''
        Y.carrier i.1 :=
  rfl

theorem
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily) :
    (genericNativeHighArbitraryWeightedCriticalScaleProxyShading
      D P hambientSource Y).shadingMass =
      affineJacobian
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) *
      (genericNativeHighArbitraryWeightedCriticalBallShading
        D P Y).shadingMass := by
  unfold Shading.shadingMass
  simp_rw [
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_carrier,
    volume_image_affineEquiv]
  rw [Finset.mul_sum]
  simp only [
    genericNativeHighArbitraryWeightedCriticalBallShading_carrier]

theorem
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_shadedUnion
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily) :
    (genericNativeHighArbitraryWeightedCriticalScaleProxyShading
      D P hambientSource Y).shadedUnion =
      genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P ''
        (genericNativeHighArbitraryWeightedCriticalBallShading
          D P Y).shadedUnion := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change
      genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P y ∈
        genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P ''
          Y.carrier i.1
    change y ∈ Y.carrier i.1 at hi
    exact ⟨y, hi, rfl⟩

theorem
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_shadedUnion_volume
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily) :
    volume
      (genericNativeHighArbitraryWeightedCriticalScaleProxyShading
        D P hambientSource Y).shadedUnion =
      affineJacobian
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P) *
      volume
        (genericNativeHighArbitraryWeightedCriticalBallShading
          D P Y).shadedUnion := by
  rw [
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_shadedUnion,
    volume_image_affineEquiv]

theorem
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_averageMultiplicity
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily) :
    (genericNativeHighArbitraryWeightedCriticalScaleProxyShading
      D P hambientSource Y).averageMultiplicity =
      (genericNativeHighArbitraryWeightedCriticalBallShading
        D P Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_shadingMass,
    genericNativeHighArbitraryWeightedCriticalScaleProxyShading_shadedUnion_volume]
  apply ENNReal.mul_div_mul_left
  · exact
      (affineJacobian_pos
        (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv
          D P)).ne'
  · exact affineJacobian_ne_top
      (genericNativeHighArbitraryWeightedCriticalScaleAffineEquiv D P)

def genericNativeHighArbitraryWeightedCriticalScaleProxyWZL3Source
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source) :
    WZL3UniformTubeSource
      (criticalScaleProxyRadius radius
        (genericNativeHighWeightedNormData D P.center P.weight).criticalScale
        (genericNativeHighArbitraryWeightedCriticalScale_pos D P))
      (GenericNativeHighArbitraryWeightedCriticalBallIndex D P) where
  family := genericNativeHighArbitraryWeightedCriticalScaleProxyFamily D P
  source := Finset.univ
  source_direction_final_half := by
    intro i _hi
    exact
      (genericNativeHighArbitraryWeightedCriticalScaleProxyGeometry
        D P hambientSource).chart i

def genericNativeHighArbitraryWeightedCriticalScaleProxyDatum
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily) :
    ActualTubeDatum
      (criticalScaleProxyRadius radius
        (genericNativeHighWeightedNormData D P.center P.weight).criticalScale
        (genericNativeHighArbitraryWeightedCriticalScale_pos D P))
      (GenericNativeHighArbitraryWeightedCriticalBallIndex D P) where
  family := genericNativeHighArbitraryWeightedCriticalScaleProxyFamily D P
  shading := genericNativeHighArbitraryWeightedCriticalScaleProxyShading
    D P hambientSource Y

#print axioms
  genericNativeHighArbitraryWeightedCriticalScaleProxyShading
#print axioms
  genericNativeHighArbitraryWeightedCriticalScaleProxyShading_shadingMass
#print axioms
  genericNativeHighArbitraryWeightedCriticalScaleProxyShading_shadedUnion_volume
#print axioms
  genericNativeHighArbitraryWeightedCriticalScaleProxyShading_averageMultiplicity
#print axioms
  genericNativeHighArbitraryWeightedCriticalScaleProxyWZL3Source
#print axioms
  genericNativeHighArbitraryWeightedCriticalScaleProxyDatum

end

end Family8Family7GenericNativeHighArbitraryWeightedProxyDatumV1
