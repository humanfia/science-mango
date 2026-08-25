import FamilyStickyGrounding.JohnRelativeBall4
import FamilyStickyGrounding.JohnTetraVolume1
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- Orthonormal coordinates on a three-dimensional affine direction. -/
def affineDirectionBasisThree (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3) :
    OrthonormalBasis (Fin 3) ℝ (affineSpan ℝ (K : Set Space)).direction :=
  (stdOrthonormalBasis ℝ (affineSpan ℝ (K : Set Space)).direction).reindex
    (finCongr hdim)

def affineDirectionEquivThree (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ]
      (affineSpan ℝ (K : Set Space)).direction :=
  (affineDirectionBasisThree K hdim).repr.symm

/-- In affine dimension three, a positive-radius Euclidean ball in affine
coordinates is contained in the convex body. -/
theorem exists_dimThree_feasible_ball (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3) :
    ∃ c : affineSpan ℝ (K : Set Space), ∃ r : ℝ, 0 < r ∧
      ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ ≤ r →
        ((affineDirectionEquivThree K hdim u :
            (affineSpan ℝ (K : Set Space)).direction) : Space) + (c : Space) ∈ K := by
  obtain ⟨c, r, hr, hball⟩ := exists_relative_closedBall_subset K
  refine ⟨c, r, hr, ?_⟩
  intro u hu
  let v := affineDirectionEquivThree K hdim u
  let y : affineSpan ℝ (K : Set Space) :=
    ⟨(v : Space) + (c : Space),
      AffineSubspace.vadd_mem_of_mem_direction v.property c.property⟩
  have hyball : y ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall]
    change dist ((v : Space) + (c : Space)) (c : Space) ≤ r
    rw [dist_eq_norm]
    simp only [add_sub_cancel_right]
    calc
      ‖(v : Space)‖ = ‖v‖ := rfl
      _ = ‖u‖ := (affineDirectionEquivThree K hdim).norm_map u
      _ ≤ r := hu
  exact hball hyball

def affineDirectionAmbientIsometryThree (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3) :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] Space :=
  (affineSpan ℝ (K : Set Space)).direction.subtypeₗᵢ.comp
    (affineDirectionEquivThree K hdim).toLinearIsometry

/-- A three-dimensional convex body contains an actual tetrahedron with
positive absolute oriented volume. -/
theorem exists_positive_tetrahedron_of_finrank_direction_affineSpan_eq_three
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space),
      ∃ r ∈ (K : Set Space), ∃ s ∈ (K : Set Space),
        0 < tetraVolume p q r s := by
  obtain ⟨c, ρ, hρ, hball⟩ := exists_dimThree_feasible_ball K hdim
  let e := affineDirectionAmbientIsometryThree K hdim
  let b : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
    fun i ↦ EuclideanSpace.single i 1
  let u₀ : EuclideanSpace ℝ (Fin 3) := ρ • b 0
  let u₁ : EuclideanSpace ℝ (Fin 3) := ρ • b 1
  let u₂ : EuclideanSpace ℝ (Fin 3) := ρ • b 2
  have hb : Orthonormal ℝ b := by
    simpa [b] using (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3))
  have heLI : LinearIndependent ℝ (fun i ↦ e (b i)) :=
    (hb.comp_linearIsometry e).linearIndependent
  have hscaledFun : LinearIndependent ℝ (fun i ↦ ρ • e (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hcomb : ∑ j, (g j * ρ) • e (b j) = 0 := by
      simpa [smul_smul] using hg
    have hi := (Fintype.linearIndependent_iff.mp heLI) (fun j ↦ g j * ρ) hcomb i
    exact (mul_eq_zero.mp hi).resolve_right hρ.ne'
  have hu₀ : ‖u₀‖ ≤ ρ := by
    simp [u₀, b, norm_smul, abs_of_pos hρ]
  have hu₁ : ‖u₁‖ ≤ ρ := by
    simp [u₁, b, norm_smul, abs_of_pos hρ]
  have hu₂ : ‖u₂‖ ≤ ρ := by
    simp [u₂, b, norm_smul, abs_of_pos hρ]
  let p : Space := c
  let q : Space := e u₀ + c
  let r : Space := e u₁ + c
  let s : Space := e u₂ + c
  have hp : p ∈ (K : Set Space) := by
    have := hball 0 (by simpa using hρ.le)
    simpa [p, e, affineDirectionAmbientIsometryThree] using this
  have hq : q ∈ (K : Set Space) := by
    simpa [q, e, affineDirectionAmbientIsometryThree] using hball u₀ hu₀
  have hr : r ∈ (K : Set Space) := by
    simpa [r, e, affineDirectionAmbientIsometryThree] using hball u₁ hu₁
  have hs : s ∈ (K : Set Space) := by
    simpa [s, e, affineDirectionAmbientIsometryThree] using hball u₂ hu₂
  refine ⟨p, hp, q, hq, r, hr, s, hs, ?_⟩
  have hqp : q - p = ρ • e (b 0) := by simp [q, p, u₀]
  have hrp : r - p = ρ • e (b 1) := by simp [r, p, u₁]
  have hsp : s - p = ρ • e (b 2) := by simp [s, p, u₂]
  have hscaled :
      LinearIndependent ℝ ![q - p, r - p, s - p] := by
    rw [hqp, hrp, hsp]
    convert hscaledFun using 1
    funext i
    fin_cases i <;> rfl
  have hgram : (Matrix.gram ℝ ![q - p, r - p, s - p]).det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hscaled
  rw [tetraVolume_def]
  apply abs_pos.mpr
  rw [tetraSignedVolume_eq_det]
  intro hdet
  apply hgram
  rw [← det_innerCoordinateMap_sq_eq_det_gram]
  simp [hdet]

#print axioms exists_dimThree_feasible_ball
#print axioms exists_positive_tetrahedron_of_finrank_direction_affineSpan_eq_three

end
end Submission.Kakeya.ConvexGeometry
