import Family8Grounding.Family8PlankThickControlActualCopyFamilyV2
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlSeedwiseAffineCopyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6AffineConvexVolumeCoreV1
open Family8PlankThickControlActualClusterV1
open Family8PlankThickControlActualCopyFamilyV2
open Family8SelectedParentAffineShadingTransportV4

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Seedwise affine transport of the `M`-aware copy family

The manuscript normalizes each selected plank/slab in its own coordinates.
Accordingly, this file allows one affine equivalence per seed.  It constructs
the actual heterogeneous image family and shading, proves the exact
Jacobian-weighted mass and volume formulae, and identifies every seed slice
with the already verified common-affine image of its literal cluster.
-/

def seedwiseAffineThickenedPlankCopyFamily
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    ConvexFamily (ThickenedPlankOccurrence D theta) :=
  fun p => affineImageConvexBody (e p.1) (D.family p.2.1)

def seedwiseAffineThickenedPlankCopyShading
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    Shading (seedwiseAffineThickenedPlankCopyFamily e D theta) where
  carrier p := e p.1 '' D.shading.carrier p.2.1
  measurable_carrier p :=
    (e p.1).toContinuousAffineEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr
      (D.shading.measurable_carrier p.2.1)
  carrier_subset p := Set.image_mono (D.shading.carrier_subset p.2.1)

@[simp] theorem seedwiseAffineThickenedPlankCopyFamily_apply
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    seedwiseAffineThickenedPlankCopyFamily e D theta p =
      affineImageConvexBody (e p.1) (D.family p.2.1) := rfl

@[simp] theorem seedwiseAffineThickenedPlankCopyShading_carrier
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    (seedwiseAffineThickenedPlankCopyShading e D theta).carrier p =
      e p.1 '' D.shading.carrier p.2.1 := rfl

abbrev seedwiseAffineThickenedPlankClusterFamily
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    ConvexFamily {j // j ∈ thickenedPlankIndices D theta i} :=
  affineImageFamily (e i) (thickenedPlankCluster D theta i).family

def seedwiseAffineThickenedPlankClusterShading
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    Shading (seedwiseAffineThickenedPlankClusterFamily e D theta i) :=
  affineImageShading (e i) (thickenedPlankCluster D theta i).shading

@[simp] theorem seedwiseAffine_copy_slice_family
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota)
    (j : {j // j ∈ thickenedPlankIndices D theta i}) :
    seedwiseAffineThickenedPlankCopyFamily e D theta ⟨i, j⟩ =
      seedwiseAffineThickenedPlankClusterFamily e D theta i j := rfl

@[simp] theorem seedwiseAffine_copy_slice_shading
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota)
    (j : {j // j ∈ thickenedPlankIndices D theta i}) :
    (seedwiseAffineThickenedPlankCopyShading e D theta).carrier ⟨i, j⟩ =
      (seedwiseAffineThickenedPlankClusterShading e D theta i).carrier j := rfl

theorem seedwiseAffineThickenedPlankCopy_shadingMass
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (seedwiseAffineThickenedPlankCopyShading e D theta).shadingMass =
      ∑ i : iota, affineJacobian (e i) *
        (∑ j ∈ thickenedPlankIndices D theta i,
          volume (D.shading.carrier j)) := by
  change (∑ p : ThickenedPlankOccurrence D theta,
    volume (e p.1 '' D.shading.carrier p.2.1)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  change (∑ y : {j // j ∈ thickenedPlankIndices D theta i},
    volume (e i '' D.shading.carrier y.1)) = _
  rw [Finset.sum_coe_sort (thickenedPlankIndices D theta i)
    (fun j => volume (e i '' D.shading.carrier j))]
  simp_rw [volume_image_affineEquiv]
  rw [Finset.mul_sum]

theorem seedwiseAffineThickenedPlankCopy_familyVolume
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    familyVolume (seedwiseAffineThickenedPlankCopyFamily e D theta) =
      ∑ i : iota, affineJacobian (e i) *
        (∑ j ∈ thickenedPlankIndices D theta i,
          volume (D.family j : Set Space)) := by
  change (∑ p : ThickenedPlankOccurrence D theta,
    volume (affineImageConvexBody (e p.1) (D.family p.2.1) : Set Space)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  change (∑ y : {j // j ∈ thickenedPlankIndices D theta i},
    volume (affineImageConvexBody (e i) (D.family y.1) : Set Space)) = _
  rw [Finset.sum_coe_sort (thickenedPlankIndices D theta i)
    (fun j => volume (affineImageConvexBody (e i) (D.family j) : Set Space))]
  simp_rw [volume_affineImageConvexBody]
  rw [Finset.mul_sum]

theorem seedwiseAffineThickenedPlankCopy_shadedUnion_eq_iUnion
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (seedwiseAffineThickenedPlankCopyShading e D theta).shadedUnion =
      ⋃ i : iota,
        (seedwiseAffineThickenedPlankClusterShading e D theta i).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨p.2, hp⟩⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i, j⟩, hj⟩

theorem seedwiseAffineThickenedPlankCluster_averageMultiplicity
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (seedwiseAffineThickenedPlankClusterShading e D theta i).averageMultiplicity =
      (thickenedPlankCluster D theta i).shading.averageMultiplicity :=
  affineImageShading_averageMultiplicity (e i) _

theorem seedwiseAffineThickenedPlankCluster_shadingDensity
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) (i : iota) :
    (seedwiseAffineThickenedPlankClusterShading e D theta i).shadingDensity =
      (thickenedPlankCluster D theta i).shading.shadingDensity :=
  affineImageShading_shadingDensity (e i) _

theorem seedwiseAffineThickenedPlankCopy_subset_seedThickeningImage
    (e : iota → Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    (seedwiseAffineThickenedPlankCopyFamily e D theta p : Set Space) ⊆
      e p.1 '' Metric.cthickening ((theta * b : NNReal) : Real)
        (D.family p.1 : Set Space) := by
  change e p.1 '' (D.family p.2.1 : Set Space) ⊆ _
  exact Set.image_mono
    (thickenedPlankCopyFamily_subset_seedThickening D theta p)

#print axioms seedwiseAffineThickenedPlankCopyFamily_apply
#print axioms seedwiseAffineThickenedPlankCopyShading_carrier
#print axioms seedwiseAffine_copy_slice_family
#print axioms seedwiseAffine_copy_slice_shading
#print axioms seedwiseAffineThickenedPlankCopy_shadingMass
#print axioms seedwiseAffineThickenedPlankCopy_familyVolume
#print axioms seedwiseAffineThickenedPlankCopy_shadedUnion_eq_iUnion
#print axioms seedwiseAffineThickenedPlankCluster_averageMultiplicity
#print axioms seedwiseAffineThickenedPlankCluster_shadingDensity
#print axioms seedwiseAffineThickenedPlankCopy_subset_seedThickeningImage

end
end Family8PlankThickControlSeedwiseAffineCopyV1
