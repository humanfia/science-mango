import FrozenTarget_ef9fbe9edb98317e
theorem M7.AffinePolynomial.image_affine : QuantumHarnessFrozenTarget := by
  intro N inst u s A
  classical
  rw [M7.AffinePolynomial.support_sum N (M7.AffinePolynomial.shifted u s A),
    M7.AffinePolynomial.substitution_support_sum N u A,
    M7.AffinePolynomial.shifted]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [M7.Action.affine, M7.AffinePolynomial.rho_add_val,
      M7.AffinePolynomial.rho_mul_val, mul_comm]
  · intro a ha b hb hab
    exact (M7.Action.affine_bijective N u s).injective hab
