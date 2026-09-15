import FrozenTarget_e89750d642613659
theorem M5.Translation.shift_quotient_polynomial : QuantumHarnessFrozenTarget := by
  classical
  intro N inst S c
  have hsupport (A : Finset (ZMod N)) :
      M5.Translation.supportPolynomial A =
        ∑ x ∈ A, (Polynomial.X : M5.BinaryPolynomial) ^ x.val := by
    change (∑ n ∈ A.image ZMod.val, (Polynomial.X : M5.BinaryPolynomial) ^ n) = _
    exact Finset.sum_image (fun a ha b hb h => ZMod.val_injective N h)
  have hshift :
      M5.Translation.supportPolynomial (M5.Translation.shift S c) =
        ∑ x ∈ S, (Polynomial.X : M5.BinaryPolynomial) ^ (x + c).val := by
    rw [hsupport]
    unfold M5.Translation.shift
    rw [Finset.sum_image]
    · simp only [add_comm]
    · intro a ha b hb h
      first
      | exact add_right_cancel h
      | exact add_left_cancel h
  have hmod (k : ℕ) :
      AdjoinRoot.mk (M5.cyclicModulus N) ((Polynomial.X : M5.BinaryPolynomial) ^ (k % N)) =
        AdjoinRoot.mk (M5.cyclicModulus N) ((Polynomial.X : M5.BinaryPolynomial) ^ k) := by
    have h := M5.SupportPolynomial.quotient_monomial_period N (k % N) (k / N)
    have hk : k % N + (k / N) * N = k := by
      simpa only [Nat.mul_comm] using Nat.mod_add_div k N
    rw [hk] at h
    exact h.symm
  rw [hshift, hsupport]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [ZMod.val_add, hmod, pow_add, map_mul]
  exact mul_comm _ _
