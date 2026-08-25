import FamilyStickyGrounding.JohnDimThreeGramSchmidt2
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv

set_option maxHeartbeats 1000000

open scoped NNReal InnerProductSpace
open Set
namespace Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap
noncomputable section

def edgeLinearImageBallThree4 (c e₀ e₁ e₂ : Space) (R : ℝ) : Set Space :=
  {x | ∃ u v w : ℝ, u ^ 2 + v ^ 2 + w ^ 2 ≤ R ^ 2 ∧
    x = c + u • e₀ + v • e₁ + w • e₂}

theorem ordered_edgeBallThree_to_boxDimensionsCertificate4
    (K : ConvexBody Space) (c e₀ e₁ e₂ : Space)
    (hli : LinearIndependent ℝ ![e₀, e₁, e₂])
    (h₁len : ‖e₁‖ ≤ ‖e₀‖) (h₂len : ‖e₂‖ ≤ ‖e₀‖)
    (hres : ‖firstResidual2 e₀ e₂‖ ≤ ‖firstResidual2 e₀ e₁‖)
    (hinner : edgeLinearImageBallThree4 c e₀ e₁ e₂ (1 / 12) ⊆ (K : Set Space))
    (houter : (K : Set Space) ⊆ edgeLinearImageBallThree4 c e₀ e₁ e₂ 3) :
    ∃ side : Fin 3 → ℝ≥0, Nonempty (BoxDimensionsCertificate 288 side K) := by
  obtain ⟨frame, L, H, J, A, Bc, Cc, hL, hH, hJ, hA, hB, hC,
      he₀, he₁, he₂⟩ := exists_ordered_edge_frame_three2 hli h₁len h₂len hres
  have hJabs : 0 < |J| := abs_pos.mpr hJ
  let side : Fin 3 → ℝ≥0 := fun i ↦
    if i = 0 then Real.toNNReal (18 * L)
    else if i = 1 then Real.toNNReal (12 * H)
    else Real.toNNReal (6 * |J|)
  let FB : FrameBox := { center := c, frame := frame, side := side }
  refine ⟨side, ⟨⟨by norm_num, FB, rfl, ?_, ?_⟩⟩⟩
  · intro x hx
    apply hinner
    let d : Fin 3 → ℝ := fun i ↦ ⟪frame i, x⟫_ℝ - ⟪frame i, c⟫_ℝ
    have hd (i : Fin 3) : |d i| ≤ (((FB.rescale (288 : ℝ≥0)⁻¹).side i : ℝ) / 2) := by
      simpa [FB, d, FrameBox.coordinateCenter, FrameBox.coordinateHalf] using
        (FB.rescale (288 : ℝ≥0)⁻¹).centeredCoordinate_abs_le_halfSide hx i
    have hd₀ : |d 0| ≤ L / 32 := by
      calc
        |d 0| ≤ (((FB.rescale (288 : ℝ≥0)⁻¹).side 0 : ℝ) / 2) := hd 0
        _ = L / 32 := by dsimp [FB, side]; rw [max_eq_left (by positivity)]; norm_num; ring
    have hd₁ : |d 1| ≤ H / 48 := by
      calc
        |d 1| ≤ (((FB.rescale (288 : ℝ≥0)⁻¹).side 1 : ℝ) / 2) := hd 1
        _ = H / 48 := by dsimp [FB, side]; rw [max_eq_left (by positivity)]; norm_num; ring
    have hd₂ : |d 2| ≤ |J| / 96 := by
      calc
        |d 2| ≤ (((FB.rescale (288 : ℝ≥0)⁻¹).side 2 : ℝ) / 2) := hd 2
        _ = |J| / 96 := by dsimp [FB, side]; rw [max_eq_left (by positivity)]; norm_num; ring
    let w : ℝ := d 2 / J
    let v : ℝ := (d 1 - Cc * w) / H
    let u : ℝ := (d 0 - A * v - Bc * w) / L
    have hwabs : |w| ≤ 1 / 96 := by
      rw [show w = d 2 / J by rfl, abs_div]
      apply (div_le_iff₀ hJabs).2
      nlinarith
    have hCwabs : |Cc * w| ≤ H / 96 := by
      rw [abs_mul]
      calc
        |Cc| * |w| ≤ H * (1 / 96) := mul_le_mul hC hwabs (abs_nonneg _) hH.le
        _ = H / 96 := by ring
    have hvabs : |v| ≤ 1 / 32 := by
      have hnum : |d 1 - Cc * w| ≤ H / 32 := by
        calc
          |d 1 - Cc * w| ≤ |d 1| + |Cc * w| := abs_sub _ _
          _ ≤ H / 48 + H / 96 := add_le_add hd₁ hCwabs
          _ = H / 32 := by ring
      rw [show v = (d 1 - Cc * w) / H by rfl, abs_div, abs_of_pos hH]
      apply (div_le_iff₀ hH).2
      nlinarith
    have hAvabs : |A * v| ≤ L / 32 := by
      rw [abs_mul]
      calc
        |A| * |v| ≤ L * (1 / 32) := mul_le_mul hA hvabs (abs_nonneg _) hL.le
        _ = L / 32 := by ring
    have hBwabs : |Bc * w| ≤ L / 96 := by
      rw [abs_mul]
      calc
        |Bc| * |w| ≤ L * (1 / 96) := mul_le_mul hB hwabs (abs_nonneg _) hL.le
        _ = L / 96 := by ring
    have huabs : |u| ≤ 7 / 96 := by
      have hnum : |d 0 - A * v - Bc * w| ≤ 7 * L / 96 := by
        calc
          |d 0 - A * v - Bc * w| ≤ |d 0 - A * v| + |Bc * w| := abs_sub _ _
          _ ≤ (|d 0| + |A * v|) + |Bc * w| := by
            have ht := abs_sub (d 0) (A * v)
            linarith
          _ ≤ (L / 32 + L / 32) + L / 96 := add_le_add (add_le_add hd₀ hAvabs) hBwabs
          _ = 7 * L / 96 := by ring
      rw [show u = (d 0 - A * v - Bc * w) / L by rfl, abs_div, abs_of_pos hL]
      apply (div_le_iff₀ hL).2
      nlinarith
    have hdSum : ∑ i, d i • frame i = x - c := by
      simpa [d, inner_sub_right] using frame.sum_repr' (x - c)
    have hwJ : w * J = d 2 := by dsimp [w]; field_simp
    have hvH : v * H = d 1 - Cc * w := by dsimp [v]; field_simp
    have huL : u * L = d 0 - A * v - Bc * w := by dsimp [u]; field_simp
    refine ⟨u, v, w, ?_, ?_⟩
    · have hu' := abs_le.mp huabs
      have hv' := abs_le.mp hvabs
      have hw' := abs_le.mp hwabs
      norm_num at hu' hv' hw' ⊢
      nlinarith [sq_nonneg (u + 7 / 96), sq_nonneg (v + 1 / 32), sq_nonneg (w + 1 / 96)]
    · calc
        x = c + ∑ i, d i • frame i := by rw [hdSum]; abel
        _ = c + d 0 • frame 0 + d 1 • frame 1 + d 2 • frame 2 := by
          rw [Fin.sum_univ_three]
          abel
        _ = c + u • e₀ + v • e₁ + w • e₂ := by
          have hd₁eq : d 1 = v * H + Cc * w := by linarith [hvH]
          have hd₀eq : d 0 = u * L + A * v + Bc * w := by linarith [huL]
          rw [hd₀eq, hd₁eq, ← hwJ, he₀, he₁, he₂]
          module
  · intro x hx
    rcases houter hx with ⟨u, v, w, huv, rfl⟩
    change c + u • e₀ + v • e₁ + w • e₂ ∈ FB.carrier
    rw [FrameBox.carrier_eq_centeredCoordinateWindow, mem_centeredCoordinateWindow_iff]
    intro i
    have huSq : u ^ 2 ≤ 9 := by nlinarith [sq_nonneg v, sq_nonneg w]
    have hvSq : v ^ 2 ≤ 9 := by nlinarith [sq_nonneg u, sq_nonneg w]
    have hwSq : w ^ 2 ≤ 9 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have huabs : |u| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
    have hvabs : |v| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
    have hwabs : |w| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
    fin_cases i
    · have hcoord : ⟪frame 0, c + u • e₀ + v • e₁ + w • e₂⟫_ℝ - ⟪frame 0, c⟫_ℝ = u * L + v * A + w * Bc := by
        rw [he₀, he₁, he₂]
        simp [inner_add_right, real_inner_smul_right, frame.inner_eq_ite]
        ring
      change abs (⟪frame 0, c + u • e₀ + v • e₁ + w • e₂⟫_ℝ - ⟪frame 0, c⟫_ℝ) ≤ ((FB.side 0 / 2 : ℝ≥0) : ℝ)
      rw [hcoord]
      have ht : |u * L + v * A + w * Bc| ≤ 9 * L := by
        calc
          |u * L + v * A + w * Bc| ≤ |u * L + v * A| + |w * Bc| := abs_add_le _ _
          _ ≤ (|u * L| + |v * A|) + |w * Bc| := by
            have hz := abs_add_le (u * L) (v * A)
            linarith
          _ = (|u| * L + |v| * |A|) + |w| * |Bc| := by rw [abs_mul, abs_mul, abs_mul, abs_of_pos hL]
          _ ≤ (3 * L + 3 * L) + 3 * L := add_le_add
            (add_le_add (mul_le_mul_of_nonneg_right huabs hL.le)
              (mul_le_mul hvabs hA (abs_nonneg _) (by norm_num)))
            (mul_le_mul hwabs hB (abs_nonneg _) (by norm_num))
          _ = 9 * L := by ring
      exact ht.trans_eq (by dsimp [FB, side]; rw [max_eq_left (by positivity)]; ring)
    · have hcoord : ⟪frame 1, c + u • e₀ + v • e₁ + w • e₂⟫_ℝ - ⟪frame 1, c⟫_ℝ = v * H + w * Cc := by
        rw [he₀, he₁, he₂]
        simp [inner_add_right, real_inner_smul_right, frame.inner_eq_ite]
        ring
      change abs (⟪frame 1, c + u • e₀ + v • e₁ + w • e₂⟫_ℝ - ⟪frame 1, c⟫_ℝ) ≤ ((FB.side 1 / 2 : ℝ≥0) : ℝ)
      rw [hcoord]
      have ht : |v * H + w * Cc| ≤ 6 * H := by
        calc
          |v * H + w * Cc| ≤ |v * H| + |w * Cc| := abs_add_le _ _
          _ = |v| * H + |w| * |Cc| := by rw [abs_mul, abs_mul, abs_of_pos hH]
          _ ≤ 3 * H + 3 * H := add_le_add
            (mul_le_mul_of_nonneg_right hvabs hH.le)
            (mul_le_mul hwabs hC (abs_nonneg _) (by norm_num))
          _ = 6 * H := by ring
      exact ht.trans_eq (by dsimp [FB, side]; rw [max_eq_left (by positivity)]; ring)
    · have hcoord : ⟪frame 2, c + u • e₀ + v • e₁ + w • e₂⟫_ℝ - ⟪frame 2, c⟫_ℝ = w * J := by
        rw [he₀, he₁, he₂]
        simp [inner_add_right, real_inner_smul_right, frame.inner_eq_ite]
      change abs (⟪frame 2, c + u • e₀ + v • e₁ + w • e₂⟫_ℝ - ⟪frame 2, c⟫_ℝ) ≤ ((FB.side 2 / 2 : ℝ≥0) : ℝ)
      rw [hcoord, abs_mul]
      have ht : |w| * |J| ≤ 3 * |J| := mul_le_mul_of_nonneg_right hwabs (abs_nonneg _)
      exact ht.trans_eq (by dsimp [FB, side]; rw [max_eq_left (by positivity)]; ring)

#print axioms ordered_edgeBallThree_to_boxDimensionsCertificate4
end
end Submission.Kakeya.ConvexGeometry
