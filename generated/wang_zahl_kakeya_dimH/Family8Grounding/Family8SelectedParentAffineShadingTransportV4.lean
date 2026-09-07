import Family8Grounding.Family8StickySelectedParentGreedyBlockFrostmanV3
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import FamilyStickyGrounding.Family6AffineConvexVolumeCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentAffineShadingTransportV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

universe u

/-- Literal image shading on a memberwise affine image family. -/
def affineImageShading
    {iota : Type u} {F : ConvexFamily iota}
    (e : Space ≃ᵃ[ℝ] Space) (Y : Shading F) :
    Shading (affineImageFamily e F) where
  carrier i := e '' Y.carrier i
  measurable_carrier i :=
    e.toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (Y.measurable_carrier i)
  carrier_subset i := Set.image_mono (Y.carrier_subset i)

@[simp] theorem affineImageShading_carrier
    {iota : Type u} {F : ConvexFamily iota}
    (e : Space ≃ᵃ[ℝ] Space) (Y : Shading F) (i : iota) :
    (affineImageShading e Y).carrier i = e '' Y.carrier i := rfl

@[simp] theorem affineImageFamily_apply
    {iota : Type u} (e : Space ≃ᵃ[ℝ] Space)
    (F : ConvexFamily iota) (i : iota) :
    affineImageFamily e F i = affineImageConvexBody e (F i) := rfl

theorem affineImageFamily_familyVolume
    {iota : Type u} [Fintype iota]
    (e : Space ≃ᵃ[ℝ] Space) (F : ConvexFamily iota) :
    familyVolume (affineImageFamily e F) =
      affineJacobian e * familyVolume F := by
  unfold familyVolume
  simp_rw [affineImageFamily_apply, volume_affineImageConvexBody]
  rw [Finset.mul_sum]

theorem affineImageShading_shadingMass
    {iota : Type u} [Fintype iota] {F : ConvexFamily iota}
    (e : Space ≃ᵃ[ℝ] Space) (Y : Shading F) :
    (affineImageShading e Y).shadingMass =
      affineJacobian e * Y.shadingMass := by
  unfold Shading.shadingMass
  simp_rw [affineImageShading_carrier, volume_image_affineEquiv]
  rw [Finset.mul_sum]

theorem affineImageShading_shadedUnion
    {iota : Type u} {F : ConvexFamily iota}
    (e : Space ≃ᵃ[ℝ] Space) (Y : Shading F) :
    (affineImageShading e Y).shadedUnion = e '' Y.shadedUnion := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, y, hy, rfl⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, y, hi, rfl⟩

theorem affineImageShading_shadedUnion_volume
    {iota : Type u} {F : ConvexFamily iota}
    (e : Space ≃ᵃ[ℝ] Space) (Y : Shading F) :
    volume (affineImageShading e Y).shadedUnion =
      affineJacobian e * volume Y.shadedUnion := by
  rw [affineImageShading_shadedUnion, volume_image_affineEquiv]

theorem affineImageShading_averageMultiplicity
    {iota : Type u} [Fintype iota] {F : ConvexFamily iota}
    (e : Space ≃ᵃ[ℝ] Space) (Y : Shading F) :
    (affineImageShading e Y).averageMultiplicity =
      Y.averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [affineImageShading_shadingMass,
    affineImageShading_shadedUnion_volume]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos e).ne'
  · exact affineJacobian_ne_top e

theorem affineImageShading_shadingDensity
    {iota : Type u} [Fintype iota] {F : ConvexFamily iota}
    (e : Space ≃ᵃ[ℝ] Space) (Y : Shading F) :
    (affineImageShading e Y).shadingDensity = Y.shadingDensity := by
  unfold Shading.shadingDensity
  rw [affineImageShading_shadingMass, affineImageFamily_familyVolume]
  apply ENNReal.mul_div_mul_left
  · exact (affineJacobian_pos e).ne'
  · exact affineJacobian_ne_top e

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Restriction of the actual aggregated parent shading to the block. -/
def selectedParentActualShading
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) :
    Shading (selectedCoarseFamily S.activeCoarseFamily B) :=
  selectedCoarseShading (parentAggregatedShading S Y) B

@[simp] theorem selectedParentActualShading_carrier
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (p : {p // p ∈ B}) :
    (selectedParentActualShading S Y B).carrier p =
      (parentAggregatedShading S Y).carrier p.1 := rfl

abbrev selectedParentAffineFamily
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) : ConvexFamily {p // p ∈ B} :=
  affineImageFamily e (selectedCoarseFamily S.activeCoarseFamily B)

/-- Literal affine image of the actual block shading. -/
def selectedParentAffineShading
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily) (B : Finset (ActiveParentIndex S)) :
    Shading (selectedParentAffineFamily e S B) :=
  affineImageShading e (selectedParentActualShading S Y B)

@[simp] theorem selectedParentAffineFamily_apply
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (p : {p // p ∈ B}) :
    selectedParentAffineFamily e S B p =
      affineImageConvexBody e (S.activeCoarseFamily p.1) := rfl

@[simp] theorem selectedParentAffineShading_carrier
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily) (B : Finset (ActiveParentIndex S))
    (p : {p // p ∈ B}) :
    (selectedParentAffineShading e S Y B).carrier p =
      e '' (parentAggregatedShading S Y).carrier p.1 := rfl

theorem selectedParentAffineFamily_familyVolume
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) :
    familyVolume (selectedParentAffineFamily e S B) =
      affineJacobian e *
        familyVolume (selectedCoarseFamily S.activeCoarseFamily B) :=
  affineImageFamily_familyVolume e _

theorem selectedParentAffineShading_shadingMass
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily) (B : Finset (ActiveParentIndex S)) :
    (selectedParentAffineShading e S Y B).shadingMass =
      affineJacobian e * (selectedParentActualShading S Y B).shadingMass :=
  affineImageShading_shadingMass e _

theorem selectedParentAffineShading_averageMultiplicity
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily) (B : Finset (ActiveParentIndex S)) :
    (selectedParentAffineShading e S Y B).averageMultiplicity =
      (selectedParentActualShading S Y B).averageMultiplicity :=
  affineImageShading_averageMultiplicity e _

theorem selectedParentAffineShading_shadingDensity
    (e : Space ≃ᵃ[ℝ] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily) (B : Finset (ActiveParentIndex S)) :
    (selectedParentAffineShading e S Y B).shadingDensity =
      (selectedParentActualShading S Y B).shadingDensity :=
  affineImageShading_shadingDensity e _

#print axioms affineImageShading
#print axioms affineImageFamily_familyVolume
#print axioms affineImageShading_shadingMass
#print axioms affineImageShading_shadedUnion
#print axioms affineImageShading_shadedUnion_volume
#print axioms affineImageShading_averageMultiplicity
#print axioms affineImageShading_shadingDensity
#print axioms selectedParentActualShading
#print axioms selectedParentAffineShading
#print axioms selectedParentAffineFamily_familyVolume
#print axioms selectedParentAffineShading_shadingMass
#print axioms selectedParentAffineShading_averageMultiplicity
#print axioms selectedParentAffineShading_shadingDensity

end
end Family8SelectedParentAffineShadingTransportV4
