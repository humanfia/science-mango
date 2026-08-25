import FamilyStickyGrounding.JohnDimTwoSimplexSandwich1
import FamilyStickyGrounding.JohnDimOneFrame1
import Mathlib.Analysis.Normed.Module.Normalize

open scoped InnerProductSpace

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem exists_frame_zero_one_eq4
    {e₀ e₁ : Space} (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1)
    (horth : ⟪e₀, e₁⟫_ℝ = 0) :
    ∃ frame : OrthonormalBasis (Fin 3) ℝ Space,
      frame 0 = e₀ ∧ frame 1 = e₁ := by
  let v : Fin 3 → Space := fun i ↦ if i = 0 then e₀ else e₁
  let s : Set (Fin 3) := {0, 1}
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · simp [v, he₀]
    · simp [v, horth]
    · simp [v, real_inner_comm, horth]
    · simp [v, he₁]
  obtain ⟨frame, hframe⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (ι := Fin 3) (by simp [Space])
  refine ⟨frame, hframe 0 ?_, hframe 1 ?_⟩ <;> simp [s]

theorem exists_ordered_edge_frame4
    {u v : Space} (hli : LinearIndependent ℝ ![u, v])
    (hvle : ‖v‖ ≤ ‖u‖) :
    ∃ frame : OrthonormalBasis (Fin 3) ℝ Space,
      ∃ L H A : ℝ,
        0 < L ∧ 0 < H ∧ |A| ≤ L ∧
        u = L • frame 0 ∧ v = A • frame 0 + H • frame 1 := by
  have hu : u ≠ 0 := hli.ne_zero 0
  let e₀ : Space := NormedSpace.normalize u
  let A : ℝ := ⟪e₀, v⟫_ℝ
  let w : Space := v - A • e₀
  have he₀ : ‖e₀‖ = 1 := NormedSpace.norm_normalize hu
  have hw : w ≠ 0 := by
    intro hw
    have hvA : v = A • e₀ := by
      apply sub_eq_zero.mp
      simpa [w] using hw
    have he₀def : e₀ = ‖u‖⁻¹ • u := by
      simp [e₀, NormedSpace.normalize]
    have hmultiple : (A * ‖u‖⁻¹) • u = v := by
      rw [mul_smul, ← he₀def]
      exact hvA.symm
    exact ((LinearIndependent.pair_iff' hu).mp hli (A * ‖u‖⁻¹)) hmultiple
  let e₁ : Space := NormedSpace.normalize w
  have he₁ : ‖e₁‖ = 1 := NormedSpace.norm_normalize hw
  have horth : ⟪e₀, e₁⟫_ℝ = 0 := by
    rw [show e₁ = ‖w‖⁻¹ • w by simp [e₁, NormedSpace.normalize],
      real_inner_smul_right]
    have hself : ⟪e₀, e₀⟫_ℝ = 1 := by simp [he₀]
    have : ⟪e₀, w⟫_ℝ = 0 := by
      rw [show w = v - A • e₀ by rfl, inner_sub_right, real_inner_smul_right,
        hself, mul_one]
      simp [A]
    rw [this, mul_zero]
  obtain ⟨frame, hframe₀, hframe₁⟩ :=
    exists_frame_zero_one_eq4 he₀ he₁ horth
  let L : ℝ := ‖u‖
  let H : ℝ := ‖w‖
  have hL : 0 < L := by simpa [L] using norm_pos_iff.mpr hu
  have hH : 0 < H := by simpa [H] using norm_pos_iff.mpr hw
  have hA : |A| ≤ L := by
    calc
      |A| = |⟪e₀, v⟫_ℝ| := rfl
      _ ≤ ‖e₀‖ * ‖v‖ := abs_real_inner_le_norm e₀ v
      _ ≤ L := by rw [he₀, one_mul]; simpa [L] using hvle
  refine ⟨frame, L, H, A, hL, hH, hA, ?_, ?_⟩
  · rw [hframe₀]
    exact (NormedSpace.norm_smul_normalize u).symm
  · rw [hframe₀, hframe₁]
    have hwrep : H • e₁ = w := NormedSpace.norm_smul_normalize w
    rw [hwrep]
    simp [w]

#print axioms exists_frame_zero_one_eq4
#print axioms exists_ordered_edge_frame4

end
end Submission.Kakeya.ConvexGeometry
