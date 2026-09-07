import Family8Grounding.Family8TubeJohnUnitRescalingV2

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnOuterEllipsoidUnitBallV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8TubeJohnUnitRescalingV2

noncomputable section

/-! # Exact image of the scale-three axis ellipsoid -/

theorem norm_sq_sum_smul_orthonormal
    (frame : OrthonormalBasis (Fin 3) Real Space) (a : Fin 3 -> Real) :
    ‖∑ i, a i • frame i‖ ^ 2 = ∑ i, (a i) ^ 2 := by
  rw [← frame.sum_sq_inner_right (∑ i, a i • frame i)]
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  rw [inner_sum]
  simp [real_inner_smul_right, frame.inner_eq_ite]

@[simp]
theorem axisEllipsoidNormalizationAffineEquiv_symm_apply
    (center : Space) (frame : OrthonormalBasis (Fin 3) Real Space)
    (radius : Fin 3 -> NNReal) (hradius : forall i, 0 < radius i)
    (y : Space) :
    (axisEllipsoidNormalizationAffineEquiv center frame radius hradius).symm y =
      center + ∑ i,
        ((3 * (radius i : Real)) * ⟪frame i, y⟫_Real) • frame i := by
  let R := axisEllipsoidNormalizationAffineEquiv center frame radius hradius
  apply R.injective
  rw [R.apply_symm_apply]
  dsimp only [R]
  rw [axisEllipsoidNormalizationAffineEquiv_apply]
  calc
    y = ∑ i, ⟪frame i, y⟫_Real • frame i := (frame.sum_repr' y).symm
    _ = ∑ i,
        (⟪frame i,
          center + ∑ j,
            ((3 * (radius j : Real)) * ⟪frame j, y⟫_Real) • frame j -
              center⟫_Real / (3 * (radius i : Real))) • frame i := by
      congr 2
      funext i
      have hcoord :
          ⟪frame i,
            center + ∑ j,
              ((3 * (radius j : Real)) * ⟪frame j, y⟫_Real) • frame j -
                center⟫_Real =
            (3 * (radius i : Real)) * ⟪frame i, y⟫_Real := by
        rw [show center + ∑ j,
          ((3 * (radius j : Real)) * ⟪frame j, y⟫_Real) • frame j - center =
            ∑ j, ((3 * (radius j : Real)) * ⟪frame j, y⟫_Real) • frame j by
              abel]
        rw [inner_sum]
        simp [real_inner_smul_right, frame.inner_eq_ite]
      rw [hcoord]
      have hri : (radius i : Real) ≠ 0 := by
        exact_mod_cast (hradius i).ne'
      field_simp

/-- The explicit diagonal affine normalization sends the displayed outer
ellipsoid exactly, not merely by containment, to the closed unit ball. -/
theorem image_axisEllipsoid_three_eq_closedBall
    (center : Space) (frame : OrthonormalBasis (Fin 3) Real Space)
    (radius : Fin 3 -> NNReal) (hradius : forall i, 0 < radius i) :
    axisEllipsoidNormalizationAffineEquiv center frame radius hradius ''
        axisEllipsoid center frame radius 3 =
      Metric.closedBall (0 : Space) 1 := by
  let R := axisEllipsoidNormalizationAffineEquiv center frame radius hradius
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, hz, hx⟩
    subst x
    rw [Metric.mem_closedBall, dist_zero_right]
    have hmap :
        R (center + ∑ i, (z i * (radius i : Real)) • frame i) =
          ∑ i, (z i / 3) • frame i := by
      dsimp only [R]
      rw [axisEllipsoidNormalizationAffineEquiv_apply]
      congr 2
      funext i
      have hcoord :
          ⟪frame i,
            center + ∑ j, (z j * (radius j : Real)) • frame j - center⟫_Real =
            z i * (radius i : Real) := by
        rw [show center + ∑ j, (z j * (radius j : Real)) • frame j - center =
          ∑ j, (z j * (radius j : Real)) • frame j by abel]
        rw [inner_sum]
        simp [real_inner_smul_right, frame.inner_eq_ite]
      rw [hcoord]
      have hri : (radius i : Real) ≠ 0 := by
        exact_mod_cast (hradius i).ne'
      field_simp
    rw [hmap]
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [norm_sq_sum_smul_orthonormal]
    rw [Fin.sum_univ_three] at hz ⊢
    norm_num at hz ⊢
    nlinarith
  · intro hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    have hySq : ‖y‖ ^ 2 <= 1 := by
      nlinarith [norm_nonneg y]
    let z : Fin 3 -> Real := fun i => 3 * ⟪frame i, y⟫_Real
    have hparseval := frame.sum_sq_inner_right y
    have hz : ∑ i, (z i) ^ 2 <= (3 : Real) ^ 2 := by
      rw [Fin.sum_univ_three] at hparseval ⊢
      dsimp only [z]
      norm_num at hparseval ⊢
      nlinarith
    refine ⟨R.symm y, ?_, R.apply_symm_apply y⟩
    refine ⟨z, hz, ?_⟩
    dsimp only [R]
    rw [axisEllipsoidNormalizationAffineEquiv_symm_apply]
    congr 2
    funext i
    dsimp only [z]
    ring

#print axioms image_axisEllipsoid_three_eq_closedBall

end
end Family8TubeJohnOuterEllipsoidUnitBallV3
