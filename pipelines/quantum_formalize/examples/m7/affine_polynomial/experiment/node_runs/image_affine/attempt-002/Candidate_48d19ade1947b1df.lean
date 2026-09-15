import FrozenTarget_48d19ade1947b1df
theorem M7.AffinePolynomial.image_affine : QuantumHarnessFrozenTarget := by
  intro N inst u s A
  classical
  rw [M7.AffinePolynomial.support_sum N,
    M7.AffinePolynomial.substitution_support_sum N]
  unfold M7.AffinePolynomial.shifted
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h : M7.Action.affine u s i = s + (u : ZMod N) * i := by
      simp [M7.Action.affine, add_comm, mul_comm]
    rw [h, M7.AffinePolynomial.rho_add_val N,
      M7.AffinePolynomial.rho_mul_val N]
  · intro a ha b hb hab
    exact (M7.Action.affine_bijective N u s).injective hab
