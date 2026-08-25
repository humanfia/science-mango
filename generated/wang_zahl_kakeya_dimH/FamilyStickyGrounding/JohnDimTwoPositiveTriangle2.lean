import FamilyStickyGrounding.JohnTransverseNonzero4

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

def affineDirectionAmbientIsometryTwo (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2) :
    EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] Space :=
  (affineSpan ℝ (K : Set Space)).direction.subtypeₗᵢ.comp
    (affineDirectionEquivTwo K hdim).toLinearIsometry

/-- An affine-dimension-two convex body contains a nondegenerate triangle. -/
theorem exists_positive_triangle_of_finrank_direction_affineSpan_eq_two
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 2) :
    ∃ p ∈ (K : Set Space), ∃ q ∈ (K : Set Space), ∃ r ∈ (K : Set Space),
      0 < triangleArea p q r := by
  obtain ⟨c, ρ, hρ, hdisk⟩ := exists_dimTwo_feasible_disk K hdim
  let e := affineDirectionAmbientIsometryTwo K hdim
  let b : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
    fun i ↦ EuclideanSpace.single i 1
  let u₀ : EuclideanSpace ℝ (Fin 2) := ρ • b 0
  let u₁ : EuclideanSpace ℝ (Fin 2) := ρ • b 1
  have hb : Orthonormal ℝ b := by
    simpa [b] using (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 2))
  have heLI : LinearIndependent ℝ (fun i ↦ e (b i)) :=
    (hb.comp_linearIsometry e).linearIndependent
  have hePair : LinearIndependent ℝ ![e (b 0), e (b 1)] := by
    convert heLI using 1
    funext i
    fin_cases i <;> rfl
  have hscaled : LinearIndependent ℝ ![ρ • e (b 0), ρ • e (b 1)] := by
    rw [LinearIndependent.pair_smul_iff hρ.ne']
    exact hePair
  have hu₀ : ‖u₀‖ ≤ ρ := by
    simp [u₀, b, norm_smul, abs_of_pos hρ]
  have hu₁ : ‖u₁‖ ≤ ρ := by
    simp [u₁, b, norm_smul, abs_of_pos hρ]
  let p : Space := c
  let q : Space := e u₀ + c
  let r : Space := e u₁ + c
  have hp : p ∈ (K : Set Space) := by
    have := hdisk 0 (by simpa using hρ.le)
    simpa [p, e, affineDirectionAmbientIsometryTwo] using this
  have hq : q ∈ (K : Set Space) := by
    simpa [q, e, affineDirectionAmbientIsometryTwo] using hdisk u₀ hu₀
  have hr : r ∈ (K : Set Space) := by
    simpa [r, e, affineDirectionAmbientIsometryTwo] using hdisk u₁ hu₁
  refine ⟨p, hp, q, hq, r, hr, ?_⟩
  rw [triangleArea_def]
  have hqp : q - p = ρ • e (b 0) := by
    simp [q, p, u₀]
  have hrp : r - p = ρ • e (b 1) := by
    simp [r, p, u₁]
  rw [hqp, hrp]
  exact norm_pos_iff.mpr (transverseVector_ne_zero_of_linearIndependent hscaled)

#print axioms exists_positive_triangle_of_finrank_direction_affineSpan_eq_two

end
end Submission.Kakeya.ConvexGeometry
