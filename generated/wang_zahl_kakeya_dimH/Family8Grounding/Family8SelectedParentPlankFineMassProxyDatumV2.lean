import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankFineMassProxyDatumV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ContractedJohnActualTubeProxyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Mass-retaining literal fine proxy on one selected parent plank

Unlike the earlier geometry-only proxy datum, this datum pushes the actual
fine shading through the same bucket affine map.  The proved carrier bridge
makes that image a genuine shading of the literal unit-axis proxy tubes.
Affine Jacobian covariance then gives exact mass scaling and preserves the
average multiplicity.  This is the analytic object needed by weighted fresh
selection.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Restriction of an actual fine shading to the literal fibre of `W`. -/
def selectedPlankFineSourceShading
    (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    Shading (fun i : SelectedPlankFineIndex S W => fine.bodyFamily i.1) where
  carrier i := Y.carrier i.1
  measurable_carrier i := Y.measurable_carrier i.1
  carrier_subset i := Y.carrier_subset i.1

@[simp] theorem selectedPlankFineSourceShading_carrier
    (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    (selectedPlankFineSourceShading Y e S B hrho label W).carrier i =
      Y.carrier i.1 := rfl

/-- Literal affine-image shading on the proxy family.  Both distortion
premises are uniform on the same selected parent fibre. -/
def selectedPlankFineMassProxyShading
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    Shading (selectedPlankFineProxyFamily
      s e S B hrho label W).bodyFamily where
  carrier i := bucketNormalizedAffineEquiv e label '' Y.carrier i.1
  measurable_carrier i :=
    (bucketNormalizedAffineEquiv e label).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i.1)
  carrier_subset i := by
    exact (Set.image_mono (Y.carrier_subset i.1)).trans
      (image_tubeCarrier_subset_affineAxisProxyTube
        (bucketNormalizedAffineEquiv e label) (fine.tubes i.1)
          (haxisLength i) hradius)

@[simp] theorem selectedPlankFineMassProxyShading_carrier
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real))
    (i : SelectedPlankFineIndex S W) :
    (selectedPlankFineMassProxyShading s Y e S B hrho label W
      haxisLength hradius).carrier i =
      bucketNormalizedAffineEquiv e label '' Y.carrier i.1 := rfl

/-- The actual mass-retaining proxy datum used by weighted fresh selection. -/
def selectedPlankFineMassProxyDatum
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    ActualTubeDatum s (SelectedPlankFineIndex S W) where
  family := selectedPlankFineProxyFamily s e S B hrho label W
  shading := selectedPlankFineMassProxyShading
    s Y e S B hrho label W haxisLength hradius

@[simp] theorem selectedPlankFineMassProxyDatum_family
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    (selectedPlankFineMassProxyDatum s Y e S B hrho label W
      haxisLength hradius).family =
      selectedPlankFineProxyFamily s e S B hrho label W := rfl

theorem selectedPlankFineMassProxyShading_shadingMass
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    (selectedPlankFineMassProxyShading s Y e S B hrho label W
      haxisLength hradius).shadingMass =
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        (selectedPlankFineSourceShading
          Y e S B hrho label W).shadingMass := by
  unfold Shading.shadingMass
  simp_rw [selectedPlankFineMassProxyShading_carrier,
    selectedPlankFineSourceShading_carrier, volume_image_affineEquiv]
  rw [Finset.mul_sum]

theorem selectedPlankFineMassProxyShading_shadedUnion
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    (selectedPlankFineMassProxyShading s Y e S B hrho label W
      haxisLength hradius).shadedUnion =
      bucketNormalizedAffineEquiv e label ''
        (selectedPlankFineSourceShading
          Y e S B hrho label W).shadedUnion := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, y, hi, rfl⟩

theorem selectedPlankFineMassProxyShading_shadedUnion_volume
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    volume (selectedPlankFineMassProxyShading s Y e S B hrho label W
      haxisLength hradius).shadedUnion =
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        volume (selectedPlankFineSourceShading
          Y e S B hrho label W).shadedUnion := by
  rw [selectedPlankFineMassProxyShading_shadedUnion,
    volume_image_affineEquiv]

/-- The common affine map preserves the actual average multiplicity of the
literal source fibre, despite the proxy tubes being larger carriers. -/
theorem selectedPlankFineMassProxyShading_averageMultiplicity
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (haxisLength : ∀ i : SelectedPlankFineIndex S W,
      ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1)
    (hradius :
      affineLinearOperatorNorm (bucketNormalizedAffineEquiv e label) *
        (delta : Real) ≤ (s : Real)) :
    (selectedPlankFineMassProxyShading s Y e S B hrho label W
      haxisLength hradius).averageMultiplicity =
      (selectedPlankFineSourceShading
        Y e S B hrho label W).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [selectedPlankFineMassProxyShading_shadingMass,
    selectedPlankFineMassProxyShading_shadedUnion_volume]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos
      (bucketNormalizedAffineEquiv e label)).ne'
  · exact affineJacobian_ne_top (bucketNormalizedAffineEquiv e label)

#print axioms selectedPlankFineSourceShading
#print axioms selectedPlankFineMassProxyShading
#print axioms selectedPlankFineMassProxyDatum
#print axioms selectedPlankFineMassProxyShading_shadingMass
#print axioms selectedPlankFineMassProxyShading_shadedUnion
#print axioms selectedPlankFineMassProxyShading_shadedUnion_volume
#print axioms selectedPlankFineMassProxyShading_averageMultiplicity

end
end Family8SelectedParentPlankFineMassProxyDatumV2
