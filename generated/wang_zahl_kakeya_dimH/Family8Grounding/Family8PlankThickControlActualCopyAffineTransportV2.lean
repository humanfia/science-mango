import Family8Grounding.Family8PlankThickControlActualCopyFamilyV2
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankThickControlActualCopyAffineTransportV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6AffineConvexVolumeCoreV1
open Family8PlankThickControlActualCopyFamilyV2
open Family8SelectedParentAffineShadingTransportV4

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Affine transport of the actual `M`-aware copy family, V2

This is the construction-level part of the slab normalization: one common
affine equivalence is applied to the literal occurrence-indexed family and
its literal shading.  Cardinality is unchanged, mass and family volume carry
the exact Jacobian, and average multiplicity and density are invariant.
-/

abbrev affineThickenedPlankCopyFamily
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    ConvexFamily (ThickenedPlankOccurrence D theta) :=
  affineImageFamily e (thickenedPlankCopyFamily D theta).family

def affineThickenedPlankCopyShading
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    Shading (affineThickenedPlankCopyFamily e D theta) :=
  affineImageShading e (thickenedPlankCopyFamily D theta).shading

@[simp] theorem affineThickenedPlankCopyFamily_apply
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    affineThickenedPlankCopyFamily e D theta p =
      affineImageConvexBody e (D.family p.2.1) := rfl

@[simp] theorem affineThickenedPlankCopyShading_carrier
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    (affineThickenedPlankCopyShading e D theta).carrier p =
      e '' D.shading.carrier p.2.1 := rfl

theorem affineThickenedPlankCopyFamily_familyVolume
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    familyVolume (affineThickenedPlankCopyFamily e D theta) =
      affineJacobian e *
        familyVolume (thickenedPlankCopyFamily D theta).family :=
  affineImageFamily_familyVolume e _

theorem affineThickenedPlankCopyShading_shadingMass
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (affineThickenedPlankCopyShading e D theta).shadingMass =
      affineJacobian e *
        (thickenedPlankCopyFamily D theta).shading.shadingMass :=
  affineImageShading_shadingMass e _

theorem affineThickenedPlankCopyShading_shadingMass_eq_sum
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (affineThickenedPlankCopyShading e D theta).shadingMass =
      affineJacobian e *
        (∑ i : iota, ∑ j ∈ thickenedPlankIndices D theta i,
          volume (D.shading.carrier j)) := by
  rw [affineThickenedPlankCopyShading_shadingMass,
    thickenedPlankCopyFamily_shadingMass]

theorem affineThickenedPlankCopyFamily_familyVolume_eq_sum
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    familyVolume (affineThickenedPlankCopyFamily e D theta) =
      affineJacobian e *
        (∑ i : iota, ∑ j ∈ thickenedPlankIndices D theta i,
          volume (D.family j : Set Space)) := by
  rw [affineThickenedPlankCopyFamily_familyVolume,
    thickenedPlankCopyFamily_familyVolume]

theorem affineThickenedPlankCopyShading_shadedUnion
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (affineThickenedPlankCopyShading e D theta).shadedUnion =
      e '' D.shading.shadedUnion := by
  change
    (affineImageShading e
      (thickenedPlankCopyFamily D theta).shading).shadedUnion = _
  rw [affineImageShading_shadedUnion,
    thickenedPlankCopyFamily_shadedUnion_eq]

theorem affineThickenedPlankCopyShading_averageMultiplicity
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (affineThickenedPlankCopyShading e D theta).averageMultiplicity =
      (thickenedPlankCopyFamily D theta).shading.averageMultiplicity :=
  affineImageShading_averageMultiplicity e _

theorem affineThickenedPlankCopyShading_shadingDensity
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    (affineThickenedPlankCopyShading e D theta).shadingDensity =
      (thickenedPlankCopyFamily D theta).shading.shadingDensity :=
  affineImageShading_shadingDensity e _

/-- The full source average multiplicity survives the actual copy construction
and an arbitrary common affine normalization. -/
theorem source_averageMultiplicity_le_affineThickenedPlankCopy
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal) :
    D.shading.averageMultiplicity ≤
      (affineThickenedPlankCopyShading e D theta).averageMultiplicity := by
  rw [affineThickenedPlankCopyShading_averageMultiplicity]
  exact source_averageMultiplicity_le_thickenedPlankCopyFamily D theta

/-- After affine normalization, each actual occurrence remains inside the
image of the thickening assigned to its seed. -/
theorem affineThickenedPlankCopyFamily_subset_seedThickeningImage
    (e : Space ≃ᵃ[Real] Space)
    (D : ShadedConvexPlankFamily iota a b) (theta : NNReal)
    (p : ThickenedPlankOccurrence D theta) :
    (affineThickenedPlankCopyFamily e D theta p : Set Space) ⊆
      e '' Metric.cthickening ((theta * b : NNReal) : Real)
        (D.family p.1 : Set Space) := by
  change e '' (D.family p.2.1 : Set Space) ⊆ _
  exact Set.image_mono
    (thickenedPlankCopyFamily_subset_seedThickening D theta p)

#print axioms affineThickenedPlankCopyFamily_apply
#print axioms affineThickenedPlankCopyShading_carrier
#print axioms affineThickenedPlankCopyFamily_familyVolume
#print axioms affineThickenedPlankCopyShading_shadingMass
#print axioms affineThickenedPlankCopyShading_shadingMass_eq_sum
#print axioms affineThickenedPlankCopyFamily_familyVolume_eq_sum
#print axioms affineThickenedPlankCopyShading_shadedUnion
#print axioms affineThickenedPlankCopyShading_averageMultiplicity
#print axioms affineThickenedPlankCopyShading_shadingDensity
#print axioms source_averageMultiplicity_le_affineThickenedPlankCopy
#print axioms affineThickenedPlankCopyFamily_subset_seedThickeningImage

end
end Family8PlankThickControlActualCopyAffineTransportV2
