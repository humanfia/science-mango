import Submission.Kakeya.ConvexGeometry.Family

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family6AffineConvexVolumeCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-- Absolute Jacobian of the linear part of an affine equivalence. -/
noncomputable def affineJacobian (e : Space ≃ᵃ[ℝ] Space) : ENNReal :=
  ENNReal.ofReal |LinearMap.det (e.linear : Space →ₗ[ℝ] Space)|

theorem affineJacobian_pos (e : Space ≃ᵃ[ℝ] Space) :
    0 < affineJacobian e := by
  rw [affineJacobian, ENNReal.ofReal_pos]
  exact abs_pos.mpr (LinearEquiv.isUnit_det' e.linear).ne_zero

theorem affineJacobian_ne_top (e : Space ≃ᵃ[ℝ] Space) :
    affineJacobian e ≠ ∞ := by
  exact ENNReal.ofReal_ne_top

/-- Exact Lebesgue-volume scaling under an affine equivalence. -/
theorem volume_image_affineEquiv (e : Space ≃ᵃ[ℝ] Space) (s : Set Space) :
    volume (e '' s) = affineJacobian e * volume s := by
  have happly : ∀ x : Space, e x = e.linear x + e 0 := by
    intro x
    exact congrFun (AffineMap.decomp e.toAffineMap) x
  have himage : e '' s = (fun y : Space ↦ e 0 + y) '' (e.linear '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.linear x, ⟨x, hx, rfl⟩,
        by simpa [add_comm] using (happly x).symm⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by rw [happly, add_comm]⟩
  rw [himage, Set.image_add_left, measure_preimage_add]
  exact volume.addHaar_image_linearMap (e.linear : Space →ₗ[ℝ] Space) s

/-- Image of a convex body under an affine equivalence. -/
noncomputable def affineImageConvexBody (e : Space ≃ᵃ[ℝ] Space)
    (K : ConvexBody Space) : ConvexBody Space where
  carrier := e '' (K : Set Space)
  convex' := Convex.affine_image e.toAffineMap K.convex
  isCompact' := K.isCompact.image e.continuous_of_finiteDimensional
  nonempty' := K.nonempty.image e

@[simp] theorem coe_affineImageConvexBody
    (e : Space ≃ᵃ[ℝ] Space) (K : ConvexBody Space) :
    (affineImageConvexBody e K : Set Space) = e '' (K : Set Space) := rfl

theorem volume_affineImageConvexBody
    (e : Space ≃ᵃ[ℝ] Space) (K : ConvexBody Space) :
    volume (affineImageConvexBody e K : Set Space) =
      affineJacobian e * volume (K : Set Space) :=
  volume_image_affineEquiv e (K : Set Space)

/-- Pull a convex test body back through an affine equivalence. -/
noncomputable def affinePreimageConvexBody
    (e : Space ≃ᵃ[ℝ] Space) (K : ConvexBody Space) : ConvexBody Space :=
  affineImageConvexBody e.symm K

@[simp] theorem coe_affinePreimageConvexBody
    (e : Space ≃ᵃ[ℝ] Space) (K : ConvexBody Space) :
    (affinePreimageConvexBody e K : Set Space) = e.symm '' (K : Set Space) :=
  rfl

theorem image_affinePreimageConvexBody
    (e : Space ≃ᵃ[ℝ] Space) (K : ConvexBody Space) :
    e '' (affinePreimageConvexBody e K : Set Space) = (K : Set Space) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩

/-- Apply an affine equivalence memberwise to a convex family. -/
noncomputable def affineImageFamily {iota : Type*}
    (e : Space ≃ᵃ[ℝ] Space) (F : ConvexFamily iota) : ConvexFamily iota :=
  fun i ↦ affineImageConvexBody e (F i)

theorem affineImage_subset_iff_subset_preimage
    (e : Space ≃ᵃ[ℝ] Space) (A B : Set Space) :
    e '' A ⊆ B ↔ A ⊆ e.symm '' B := by
  constructor
  · intro h x hx
    exact ⟨e x, h ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨z, hz, hzx⟩ := h hx
    have : z = e x := by
      apply e.symm.injective
      simpa using hzx
    simpa [this] using hz

theorem volume_eq_affineJacobian_mul_preimage
    (e : Space ≃ᵃ[ℝ] Space) (K : ConvexBody Space) :
    volume (K : Set Space) =
      affineJacobian e * volume (affinePreimageConvexBody e K : Set Space) := by
  calc
    volume (K : Set Space) =
        volume (e '' (affinePreimageConvexBody e K : Set Space)) := by
      rw [image_affinePreimageConvexBody]
    _ = affineJacobian e *
        volume (affinePreimageConvexBody e K : Set Space) :=
      volume_image_affineEquiv e _

#print axioms volume_image_affineEquiv
#print axioms volume_affineImageConvexBody
#print axioms image_affinePreimageConvexBody
#print axioms volume_eq_affineJacobian_mul_preimage

end
end Family6AffineConvexVolumeCoreV1
