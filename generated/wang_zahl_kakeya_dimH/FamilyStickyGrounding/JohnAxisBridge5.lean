import Submission.Kakeya.ConvexFactoring.CertifiedSlabOverlap
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv

open scoped NNReal InnerProductSpace
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- An axis ellipsoid, defined as the diagonal image of a coefficient ball.
This definition also permits zero semiaxes. -/
def axisEllipsoid (center : Space) (frame : OrthonormalBasis (Fin 3) ℝ Space)
    (radius : Fin 3 → ℝ≥0) (scale : ℝ) : Set Space :=
  {x | ∃ z : Fin 3 → ℝ,
    (∑ i, (z i) ^ 2) ≤ scale ^ 2 ∧
      x = center + ∑ i, (z i * (radius i : ℝ)) • frame i}

/-- The exact geometric output needed from a 3D John theorem.  Its fields are
ellipsoid/body comparisons, not box comparisons. -/
structure JohnAxisWitness (K : ConvexBody Space) where
  center : Space
  frame : OrthonormalBasis (Fin 3) ℝ Space
  radius : Fin 3 → ℝ≥0
  inner : axisEllipsoid center frame radius 1 ⊆ (K : Set Space)
  outer : (K : Set Space) ⊆ axisEllipsoid center frame radius 3

/-- A factor-three John ellipsoid yields the repository's box certificate
with the explicit universal constant six.  Both box comparisons are derived. -/
theorem JohnAxisWitness.to_boxDimensionsCertificate
    {K : ConvexBody Space} (w : JohnAxisWitness K) :
    ∃ side : Fin 3 → ℝ≥0, Nonempty (BoxDimensionsCertificate 6 side K) := by
  let side : Fin 3 → ℝ≥0 := fun i ↦ 6 * w.radius i
  let B : FrameBox :=
    { center := w.center
      frame := w.frame
      side := side }
  refine ⟨side, ⟨⟨by norm_num, B, rfl, ?_, ?_⟩⟩⟩
  · intro x hx
    apply w.inner
    let d : Fin 3 → ℝ := fun i ↦
      ⟪w.frame i, x⟫_ℝ - ⟪w.frame i, w.center⟫_ℝ
    let z : Fin 3 → ℝ := fun i ↦
      if h : (w.radius i : ℝ) = 0 then 0 else d i / (w.radius i : ℝ)
    have hd (i : Fin 3) : |d i| ≤ (w.radius i : ℝ) / 2 := by
      have h := (B.rescale (6 : ℝ≥0)⁻¹).centeredCoordinate_abs_le_halfSide hx i
      simpa [B, side, d] using h
    have hzmul (i : Fin 3) : z i * (w.radius i : ℝ) = d i := by
      by_cases hri : (w.radius i : ℝ) = 0
      · have hdi : d i = 0 := by
          have h := hd i
          rw [hri] at h
          norm_num at h
          exact h
        simp [z, hri, hdi]
      · dsimp [z]
        rw [if_neg hri]
        exact div_mul_cancel₀ _ hri
    have hzabs (i : Fin 3) : |z i| ≤ (2 : ℝ)⁻¹ := by
      by_cases hri : (w.radius i : ℝ) = 0
      · simp [z, hri]
      · have hripos : 0 < (w.radius i : ℝ) :=
          lt_of_le_of_ne NNReal.zero_le_coe (Ne.symm hri)
        have hdi := abs_le.mp (hd i)
        simp only [z, hri]
        rw [abs_le]
        constructor
        · apply (le_div_iff₀ hripos).2
          nlinarith [hdi.1]
        · apply (div_le_iff₀ hripos).2
          nlinarith [hdi.2]
    have hzsq (i : Fin 3) : (z i) ^ 2 ≤ (4 : ℝ)⁻¹ := by
      have hzi := abs_le.mp (hzabs i)
      have hp : 0 ≤ ((2 : ℝ)⁻¹ - z i) * ((2 : ℝ)⁻¹ + z i) :=
        mul_nonneg (sub_nonneg.mpr hzi.2) (by linarith [hzi.1])
      nlinarith
    refine ⟨z, ?_, ?_⟩
    · rw [Fin.sum_univ_three]
      norm_num
      nlinarith [hzsq 0, hzsq 1, hzsq 2]
    · have hsum : ∑ i, d i • w.frame i = x - w.center := by
        simpa [d, inner_sub_right] using w.frame.sum_repr' (x - w.center)
      calc
        x = w.center + (x - w.center) := by abel
        _ = w.center + ∑ i, d i • w.frame i := by rw [hsum]
        _ = w.center + ∑ i, (z i * (w.radius i : ℝ)) • w.frame i := by
          congr 2
          funext i
          rw [hzmul i]
  · intro x hx
    rcases w.outer hx with ⟨z, hz, rfl⟩
    change w.center + ∑ i, (z i * (w.radius i : ℝ)) • w.frame i ∈ B.carrier
    rw [FrameBox.carrier_eq_centeredCoordinateWindow,
      mem_centeredCoordinateWindow_iff]
    intro i
    have hziSq : (z i) ^ 2 ≤ 9 := by
      calc
        (z i) ^ 2 ≤ ∑ j, (z j) ^ 2 :=
          Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i)
        _ ≤ 3 ^ 2 := hz
        _ = 9 := by norm_num
    have hzi : |z i| ≤ 3 := by
      rw [abs_le]
      constructor <;> nlinarith
    change abs
      (⟪w.frame i, w.center + ∑ j, (z j * (w.radius j : ℝ)) • w.frame j⟫_ℝ -
        ⟪w.frame i, w.center⟫_ℝ) ≤ ((B.side i / 2 : ℝ≥0) : ℝ)
    have hcoord :
        ⟪w.frame i, w.center + ∑ j, (z j * (w.radius j : ℝ)) • w.frame j⟫_ℝ -
          ⟪w.frame i, w.center⟫_ℝ = z i * (w.radius i : ℝ) := by
      rw [inner_add_right, add_sub_cancel_left, inner_sum]
      simp only [real_inner_smul_right, w.frame.inner_eq_ite]
      simp
    rw [hcoord]
    dsimp [B, side]
    rw [abs_mul, abs_of_nonneg NNReal.zero_le_coe]
    calc
      |z i| * (w.radius i : ℝ) ≤ 3 * (w.radius i : ℝ) :=
        mul_le_mul_of_nonneg_right hzi NNReal.zero_le_coe
      _ = 6 * (w.radius i : ℝ) / 2 := by ring

/-- This is only a conditional bridge: the premise is precisely the missing
actual John existence theorem. -/
theorem exists_boxDimensionsCertificate_six_of_johnAxisWitness
    (hJohn : ∀ K : ConvexBody Space, Nonempty (JohnAxisWitness K)) :
    ∀ K : ConvexBody Space,
      ∃ side : Fin 3 → ℝ≥0, Nonempty (BoxDimensionsCertificate 6 side K) := by
  intro K
  rcases hJohn K with ⟨w⟩
  rcases w.to_boxDimensionsCertificate with ⟨side, ⟨cert⟩⟩
  exact ⟨side, ⟨cert⟩⟩

#print axioms JohnAxisWitness.to_boxDimensionsCertificate
#print axioms exists_boxDimensionsCertificate_six_of_johnAxisWitness

end
end Submission.Kakeya.ConvexGeometry
