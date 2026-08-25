import FamilyStickyGrounding.JohnDimTwoGramSchmidt4

open scoped InnerProductSpace

namespace Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya
noncomputable section

def firstResidual2 (e v : Space) : Space :=
  v - ⟪NormedSpace.normalize e, v⟫_ℝ • NormedSpace.normalize e

theorem independent_first_pair_of_three2
    {e₀ e₁ e₂ : Space} (h : LinearIndependent ℝ ![e₀, e₁, e₂]) :
    LinearIndependent ℝ ![e₀, e₁] := by
  let f : Fin 2 → Fin 3 := fun i ↦ ⟨i.1, by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin 3 ↦ x.val) hij
  have hc := h.comp f hf
  convert hc using 1
  funext i
  fin_cases i <;> rfl

theorem exists_ordered_edge_frame_three2
    {e₀ e₁ e₂ : Space} (hli : LinearIndependent ℝ ![e₀, e₁, e₂])
    (h₁len : ‖e₁‖ ≤ ‖e₀‖) (h₂len : ‖e₂‖ ≤ ‖e₀‖)
    (hres : ‖firstResidual2 e₀ e₂‖ ≤ ‖firstResidual2 e₀ e₁‖) :
    ∃ frame : OrthonormalBasis (Fin 3) ℝ Space,
      ∃ L H J A B C : ℝ,
        0 < L ∧ 0 < H ∧ J ≠ 0 ∧
        |A| ≤ L ∧ |B| ≤ L ∧ |C| ≤ H ∧
        e₀ = L • frame 0 ∧
        e₁ = A • frame 0 + H • frame 1 ∧
        e₂ = B • frame 0 + C • frame 1 + J • frame 2 := by
  have hpair := independent_first_pair_of_three2 hli
  obtain ⟨frame, L, H, A, hL, hH, hA, he₀, he₁⟩ :=
    exists_ordered_edge_frame4 hpair h₁len
  let B : ℝ := ⟪frame 0, e₂⟫_ℝ
  let C : ℝ := ⟪frame 1, e₂⟫_ℝ
  let J : ℝ := ⟪frame 2, e₂⟫_ℝ
  have he₀norm : NormedSpace.normalize e₀ = frame 0 := by
    rw [he₀, NormedSpace.normalize_smul_of_pos hL]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (frame.norm_eq_one 0)
  have he₀normL : ‖e₀‖ = L := by
    rw [he₀, norm_smul, Real.norm_eq_abs, abs_of_pos hL, frame.norm_eq_one, mul_one]
  have hAcoord : ⟪frame 0, e₁⟫_ℝ = A := by
    rw [he₁]
    simp [inner_add_right, real_inner_smul_right, frame.inner_eq_ite]
  have hres₁ : firstResidual2 e₀ e₁ = H • frame 1 := by
    rw [firstResidual2, he₀norm, hAcoord, he₁]
    module
  have hB : |B| ≤ L := by
    calc
      |B| = |⟪frame 0, e₂⟫_ℝ| := rfl
      _ ≤ ‖frame 0‖ * ‖e₂‖ := abs_real_inner_le_norm _ _
      _ ≤ L := by rw [frame.norm_eq_one, one_mul]; exact h₂len.trans_eq he₀normL
  have hCres : C = ⟪frame 1, firstResidual2 e₀ e₂⟫_ℝ := by
    simp [firstResidual2, he₀norm, C, inner_sub_right, real_inner_smul_right,
      frame.inner_eq_ite]
  have hC : |C| ≤ H := by
    rw [hCres]
    calc
      |⟪frame 1, firstResidual2 e₀ e₂⟫_ℝ| ≤
          ‖frame 1‖ * ‖firstResidual2 e₀ e₂‖ := abs_real_inner_le_norm _ _
      _ ≤ H := by
        rw [frame.norm_eq_one, one_mul]
        calc
          ‖firstResidual2 e₀ e₂‖ ≤ ‖firstResidual2 e₀ e₁‖ := hres
          _ = H := by rw [hres₁, norm_smul, Real.norm_eq_abs, abs_of_pos hH,
            frame.norm_eq_one, mul_one]
  have he₂ : e₂ = B • frame 0 + C • frame 1 + J • frame 2 := by
    simpa [B, C, J, Fin.sum_univ_three] using (frame.sum_repr' e₂).symm
  have hJ : J ≠ 0 := by
    intro hJ
    have hrel :
        (C * A - B * H) • e₀ + (-C * L) • e₁ + (H * L) • e₂ = 0 := by
      rw [he₀, he₁, he₂, hJ, zero_smul, add_zero]
      module
    let g : Fin 3 → ℝ := ![C * A - B * H, -C * L, H * L]
    have hsum : ∑ i, g i • ![e₀, e₁, e₂] i = 0 := by
      rw [Fin.sum_univ_three]
      simpa [g] using hrel
    have hg := (Fintype.linearIndependent_iff.mp hli g hsum) 2
    have hHL : H * L = 0 := by simpa [g] using hg
    exact (mul_ne_zero hH.ne' hL.ne') hHL
  exact ⟨frame, L, H, J, A, B, C, hL, hH, hJ, hA, hB, hC,
    he₀, he₁, he₂⟩

#print axioms independent_first_pair_of_three2
#print axioms exists_ordered_edge_frame_three2

end
end Submission.Kakeya.ConvexGeometry
