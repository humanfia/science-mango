import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyShadingV1
import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8WeightedCanonicalCriticalScaleProxyAverageV2

open Submission.Kakeya.ConvexGeometry
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyShadingV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-! Affine critical-scale normalization preserves average multiplicity on
the literal critical-ball shading.  The result is independent of how the
weighted canonical datum was produced. -/

def weightedCanonicalCriticalBallShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily) :
    Shading (S.family.restrictTo W.criticalBall).bodyFamily where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

theorem weightedCanonicalCriticalScaleProxyShading_shadedUnion
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily)
    (haxis : ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)‖ ≤ 1)
    (htransverse :
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) *
            (radius : Real) ≤
        (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : Real)) :
    (weightedCanonicalCriticalScaleProxyShading
      S W Y haxis htransverse).shadedUnion =
      weightedCanonicalCriticalScaleAffineEquiv S W ''
        (weightedCanonicalCriticalBallShading S W Y).shadedUnion := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, ⟨y, hi, rfl⟩⟩

theorem weightedCanonicalCriticalScaleProxyShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily)
    (haxis : ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)‖ ≤ 1)
    (htransverse :
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) *
            (radius : Real) ≤
        (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : Real)) :
    (weightedCanonicalCriticalScaleProxyShading
      S W Y haxis htransverse).shadingMass =
      affineJacobian (weightedCanonicalCriticalScaleAffineEquiv S W) *
        (weightedCanonicalCriticalBallShading S W Y).shadingMass := by
  unfold Shading.shadingMass
  simp_rw [weightedCanonicalCriticalScaleProxyShading,
    volume_image_affineEquiv]
  rw [Finset.mul_sum]
  simp only [weightedCanonicalCriticalBallShading]

theorem weightedCanonicalCriticalScaleProxyShading_averageMultiplicity
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily)
    (haxis : ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)‖ ≤ 1)
    (htransverse :
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) *
            (radius : Real) ≤
        (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : Real)) :
    (weightedCanonicalCriticalScaleProxyShading
      S W Y haxis htransverse).averageMultiplicity =
      (weightedCanonicalCriticalBallShading S W Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [weightedCanonicalCriticalScaleProxyShading_shadingMass,
    weightedCanonicalCriticalScaleProxyShading_shadedUnion,
    volume_image_affineEquiv]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos
      (weightedCanonicalCriticalScaleAffineEquiv S W)).ne'
  · exact affineJacobian_ne_top
      (weightedCanonicalCriticalScaleAffineEquiv S W)

#print axioms weightedCanonicalCriticalScaleProxyShading_averageMultiplicity

end

end Family8WeightedCanonicalCriticalScaleProxyAverageV2
