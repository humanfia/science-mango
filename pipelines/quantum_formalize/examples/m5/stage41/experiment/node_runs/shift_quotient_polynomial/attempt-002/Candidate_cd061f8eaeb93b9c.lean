import FrozenTarget_cd061f8eaeb93b9c
theorem M5.Translation.shift_quotient_polynomial : QuantumHarnessFrozenTarget := by
  classical
  intro N inst S c
  have hsupport (A : Finset (ZMod N)) :
      M5.Translation.supportPolynomial A =
        ∑ x ∈ A, (Polynomial.X : M5.BinaryPolynomial) ^ x.val := by
    change (∑ n ∈ A.image ZMod.val, (Polynomial.X : M5.BinaryPolynomial) ^ n) = _
    apply Finset.sum_image
    intro x hx y hy h
    have hc := congrArg (fun n : ℕ => (n : ZMod N)) h
    simpa using hc
  rw [hsupport, hsupport]
  unfold M5.Translation.shift
  rw [Finset.sum_image]
  · simp only [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [ZMod.val_add]
    have hp := M5.SupportPolynomial.quotient_monomial_period N
      ((c.val + x.val) % N) ((c.val + x.val) / N)
    have he : (c.val + x.val) % N + (c.val + x.val) / N * N =
        c.val + x.val := by
      simpa [Nat.mul_comm] using Nat.mod_add_div (c.val + x.val) N
    rw [he] at hp
    rw [← hp, pow_add, map_mul]
  · intro x hx y hy h
    exact add_left_cancel h
