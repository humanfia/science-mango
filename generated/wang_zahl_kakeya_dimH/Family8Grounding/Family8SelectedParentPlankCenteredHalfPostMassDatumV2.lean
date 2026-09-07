import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostCarrierV1
import Family8Grounding.Family8SelectedParentPlankFineMassProxyDatumV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredHalfPostMassDatumV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Mass on the centered half-post selected-plank proxy

The fixed-`W` centered half-post map has automatic unit-axis control and B2
support. Pushing the actual fine shading through this same affine map gives
an honest shading of the literal centered proxy family. Its mass and shaded
union acquire the same exact affine Jacobian, so average multiplicity is
preserved without any loss.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

def centeredHalfPostSelectedPlankFineMassShading
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real)) :
    Shading (centeredHalfPostSelectedPlankFineProxyFamily
      s e S B hrho label hplank W).bodyFamily where
  carrier i := centeredHalfPostBucketAffineEquiv
    e S B hrho label hplank W '' Y.carrier i.1
  measurable_carrier i :=
    (centeredHalfPostBucketAffineEquiv
      e S B hrho label hplank W).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
        (Y.measurable_carrier i.1)
  carrier_subset i :=
    (Set.image_mono (Y.carrier_subset i.1)).trans
      (centeredHalfPost_image_tubeCarrier_subset_proxy
        s e S B hrho label hplank W hradius i)

@[simp] theorem centeredHalfPostSelectedPlankFineMassShading_carrier
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real))
    (i : SelectedPlankFineIndex S W) :
    (centeredHalfPostSelectedPlankFineMassShading
      s Y e S B hrho label hplank W hradius).carrier i =
      centeredHalfPostBucketAffineEquiv e S B hrho label hplank W ''
        Y.carrier i.1 := rfl

def centeredHalfPostSelectedPlankFineMassDatum
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real)) :
    ActualTubeDatum s (SelectedPlankFineIndex S W) where
  family := centeredHalfPostSelectedPlankFineProxyFamily
    s e S B hrho label hplank W
  shading := centeredHalfPostSelectedPlankFineMassShading
    s Y e S B hrho label hplank W hradius

@[simp] theorem centeredHalfPostSelectedPlankFineMassDatum_family
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real)) :
    (centeredHalfPostSelectedPlankFineMassDatum
      s Y e S B hrho label hplank W hradius).family =
      centeredHalfPostSelectedPlankFineProxyFamily
        s e S B hrho label hplank W := rfl

theorem centeredHalfPostSelectedPlankFineMassShading_shadingMass
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real)) :
    (centeredHalfPostSelectedPlankFineMassShading
      s Y e S B hrho label hplank W hradius).shadingMass =
      affineJacobian
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
          (selectedPlankFineSourceShading
            Y e S B hrho label W).shadingMass := by
  unfold Shading.shadingMass
  simp_rw [centeredHalfPostSelectedPlankFineMassShading_carrier,
    selectedPlankFineSourceShading_carrier, volume_image_affineEquiv]
  rw [Finset.mul_sum]

theorem centeredHalfPostSelectedPlankFineMassShading_shadedUnion
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real)) :
    (centeredHalfPostSelectedPlankFineMassShading
      s Y e S B hrho label hplank W hradius).shadedUnion =
      centeredHalfPostBucketAffineEquiv e S B hrho label hplank W ''
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

theorem centeredHalfPostSelectedPlankFineMassShading_shadedUnion_volume
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real)) :
    volume (centeredHalfPostSelectedPlankFineMassShading
      s Y e S B hrho label hplank W hradius).shadedUnion =
      affineJacobian
        (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
          volume (selectedPlankFineSourceShading
            Y e S B hrho label W).shadedUnion := by
  rw [centeredHalfPostSelectedPlankFineMassShading_shadedUnion,
    volume_image_affineEquiv]

theorem centeredHalfPostSelectedPlankFineMassShading_averageMultiplicity
    (s : NNReal) (Y : Shading fine.bodyFamily)
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W) *
        (delta : Real) ≤ (s : Real)) :
    (centeredHalfPostSelectedPlankFineMassShading
      s Y e S B hrho label hplank W hradius).averageMultiplicity =
      (selectedPlankFineSourceShading
        Y e S B hrho label W).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [centeredHalfPostSelectedPlankFineMassShading_shadingMass,
    centeredHalfPostSelectedPlankFineMassShading_shadedUnion_volume]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos
      (centeredHalfPostBucketAffineEquiv
        e S B hrho label hplank W)).ne'
  · exact affineJacobian_ne_top
      (centeredHalfPostBucketAffineEquiv e S B hrho label hplank W)

#print axioms centeredHalfPostSelectedPlankFineMassShading
#print axioms centeredHalfPostSelectedPlankFineMassDatum
#print axioms centeredHalfPostSelectedPlankFineMassShading_shadingMass
#print axioms centeredHalfPostSelectedPlankFineMassShading_shadedUnion
#print axioms centeredHalfPostSelectedPlankFineMassShading_shadedUnion_volume
#print axioms centeredHalfPostSelectedPlankFineMassShading_averageMultiplicity

end
end Family8SelectedParentPlankCenteredHalfPostMassDatumV2
