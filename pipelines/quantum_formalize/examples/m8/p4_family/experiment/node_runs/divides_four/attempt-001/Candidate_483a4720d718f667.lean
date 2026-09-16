import FrozenTarget_483a4720d718f667
theorem M8.P4Family.divides_four : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, 4 ∣ N → M8.P4Family.polynomial ∣ M6.Cyclic.modulus N
  intro N hN
  rcases hN with ⟨k, rfl⟩
  have h : ∀ k : ℕ, M8.P4Family.polynomial ∣ (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (4 * k) - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨q * Polynomial.X ^ 4 + (Polynomial.X - 1), ?_⟩
      rw [Nat.mul_succ, pow_add]
      calc
        Polynomial.X ^ (4 * k) * Polynomial.X ^ 4 - 1 =
            (Polynomial.X ^ (4 * k) - 1) * Polynomial.X ^ 4 + (Polynomial.X ^ 4 - 1) := by ring
        _ = M8.P4Family.polynomial * (q * Polynomial.X ^ 4 + (Polynomial.X - 1)) := by
          rw [hq]
          unfold M8.P4Family.polynomial
          ring
  first
  | simpa only [M6.Cyclic.modulus] using h k
  | have hneg : -(1 : M6.Cyclic.BinaryPolynomial) = 1 := by
      ext n
      by_cases hn : n = 0
      · subst n
        norm_num
      · simp [Polynomial.coeff_one, hn]
    simpa [M6.Cyclic.modulus, sub_eq_add_neg, hneg] using h k
