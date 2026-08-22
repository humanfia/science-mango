import Submission.Kakeya.ConvexFactoring.TransverseCoordinateOverlap
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Determinant and angle bridges in three dimensions

This module identifies the determinant of `innerCoordinateMap` with the scalar
triple product and its square with the corresponding Gram determinant.  For a
unit frame whose first vector is perpendicular to the other two, it then
identifies the absolute determinant with both
`Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2)` and the sine of the angle between `u` and `v`.
These identities turn angular transversality into the nonvanishing hypothesis
used by the coordinate-window volume formulas.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix

namespace Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- In the standard Euclidean basis, the matrix of `innerCoordinateMap` has
the input vectors as its rows. -/
theorem toMatrix_innerCoordinateMap_eq_rows (v : Fin 3 → Space) :
    (innerCoordinateMap v).toMatrix
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis =
      fun i j ↦ WithLp.ofLp (v i) j := by
  ext i j
  simpa [LinearMap.toMatrix_apply, innerCoordinateMap_apply] using
    EuclideanSpace.inner_basisFun_real (ι := Fin 3) (v i) j

/-- The determinant of the coordinate map is the determinant of the matrix
whose rows are the underlying coordinate vectors. -/
theorem det_innerCoordinateMap_eq_matrix_det (v : Fin 3 → Space) :
    LinearMap.det (innerCoordinateMap v) =
      Matrix.det (fun i j ↦ WithLp.ofLp (v i) j) := by
  rw [← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (innerCoordinateMap v)]
  rw [toMatrix_innerCoordinateMap_eq_rows]

/-- In dimension three, the coordinate determinant is the scalar triple
product of the underlying coordinate vectors. -/
theorem det_innerCoordinateMap_vec3_eq_tripleProduct (a b c : Space) :
    LinearMap.det (innerCoordinateMap ![a, b, c]) =
      WithLp.ofLp a ⬝ᵥ (WithLp.ofLp b ⨯₃ WithLp.ofLp c) := by
  rw [det_innerCoordinateMap_eq_matrix_det]
  rw [show (fun i j ↦ WithLp.ofLp (![a, b, c] i) j) =
      ![WithLp.ofLp a, WithLp.ofLp b, WithLp.ofLp c] by
    ext i j
    fin_cases i <;> rfl]
  exact (triple_product_eq_det
    (WithLp.ofLp a) (WithLp.ofLp b) (WithLp.ofLp c)).symm

/-- Gram determinant identity for the three rows of `innerCoordinateMap`. -/
theorem det_innerCoordinateMap_sq_eq_det_gram (v : Fin 3 → Space) :
    LinearMap.det (innerCoordinateMap v) ^ 2 =
      (Matrix.gram ℝ v).det := by
  rw [det_innerCoordinateMap_eq_matrix_det]
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j ↦ WithLp.ofLp (v i) j
  have hgram : Matrix.gram ℝ v = A * A.transpose := by
    ext i j
    simp only [Matrix.gram_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Matrix.mul_apply]
    simp only [A]
    apply Finset.sum_congr rfl
    intro k hk
    change (v j).ofLp k * (v i).ofLp k =
      (v i).ofLp k * (v j).ofLp k
    ring
  rw [hgram, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- If `e`, `u`, and `v` are unit vectors and `e` is perpendicular to both
`u` and `v`, the squared coordinate determinant is the squared transverse
quantity `1 - ⟪u,v⟫²`. -/
theorem det_innerCoordinateMap_sq_eq_one_sub_inner_sq
    (e u v : Space)
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (heu : ⟪e, u⟫_ℝ = 0) (hev : ⟪e, v⟫_ℝ = 0) :
    LinearMap.det (innerCoordinateMap ![e, u, v]) ^ 2 =
      1 - ⟪u, v⟫_ℝ ^ 2 := by
  rw [det_innerCoordinateMap_sq_eq_det_gram]
  have hee : ⟪e, e⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  have huu : ⟪u, u⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hvv : ⟪v, v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hue : ⟪u, e⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact heu
  have hve : ⟪v, e⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hev
  have hvu : ⟪v, u⟫_ℝ = ⟪u, v⟫_ℝ := real_inner_comm u v
  rw [Matrix.det_fin_three]
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  rw [hee, huu, hvv, heu, hue, hev, hve, hvu]
  ring

/-- Exact square-root form of the transverse determinant. -/
theorem abs_det_innerCoordinateMap_eq_sqrt_one_sub_inner_sq
    (e u v : Space)
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (heu : ⟪e, u⟫_ℝ = 0) (hev : ⟪e, v⟫_ℝ = 0) :
    |LinearMap.det (innerCoordinateMap ![e, u, v])| =
      Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by
  calc
    |LinearMap.det (innerCoordinateMap ![e, u, v])| =
        Real.sqrt (LinearMap.det (innerCoordinateMap ![e, u, v]) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by
      rw [det_innerCoordinateMap_sq_eq_one_sub_inner_sq e u v he hu hv heu hev]

/-- For a unit transverse frame, the absolute determinant is exactly the sine
of the angle between the two unit directions. -/
theorem abs_det_innerCoordinateMap_eq_sin_angle
    (e u v : Space)
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (heu : ⟪e, u⟫_ℝ = 0) (hev : ⟪e, v⟫_ℝ = 0) :
    |LinearMap.det (innerCoordinateMap ![e, u, v])| =
      Real.sin (InnerProductGeometry.angle u v) := by
  rw [abs_det_innerCoordinateMap_eq_sqrt_one_sub_inner_sq e u v he hu hv heu hev]
  rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hu hv]
  rw [show 1 - Real.cos (InnerProductGeometry.angle u v) ^ 2 =
      Real.sin (InnerProductGeometry.angle u v) ^ 2 by
    nlinarith [Real.sin_sq_add_cos_sq (InnerProductGeometry.angle u v)]]
  exact Real.sqrt_sq (InnerProductGeometry.sin_angle_nonneg u v)

/-- A sine transversality lower bound is therefore a determinant lower bound. -/
theorem le_abs_det_innerCoordinateMap_of_le_sin_angle
    (e u v : Space) (τ : ℝ)
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (heu : ⟪e, u⟫_ℝ = 0) (hev : ⟪e, v⟫_ℝ = 0)
    (hτ : τ ≤ Real.sin (InnerProductGeometry.angle u v)) :
    τ ≤ |LinearMap.det (innerCoordinateMap ![e, u, v])| := by
  rw [abs_det_innerCoordinateMap_eq_sin_angle e u v he hu hv heu hev]
  exact hτ

/-- Positive angular transversality supplies the nonzero determinant required
by the exact coordinate-window volume formula. -/
theorem det_innerCoordinateMap_ne_zero_of_sin_angle_pos
    (e u v : Space)
    (he : ‖e‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (heu : ⟪e, u⟫_ℝ = 0) (hev : ⟪e, v⟫_ℝ = 0)
    (hangle : 0 < Real.sin (InnerProductGeometry.angle u v)) :
    LinearMap.det (innerCoordinateMap ![e, u, v]) ≠ 0 := by
  intro hzero
  have hdet := abs_det_innerCoordinateMap_eq_sin_angle
    e u v he hu hv heu hev
  rw [hzero, abs_zero] at hdet
  linarith

end

end Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
