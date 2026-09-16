import FrozenTarget_a69b8559bbaaa0ef
theorem M8.P3Family.divides_modulus : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, 3 ∣ N → M8.P3Family.polynomial ∣ M6.Cyclic.modulus N
  intro N hN
  obtain ⟨k, rfl⟩ := hN
  have h : ∀ k : ℕ, M8.P3Family.polynomial ∣
      (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (3 * k) - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨q * Polynomial.X ^ 3 + (Polynomial.X - 1), ?_⟩
      calc
        Polynomial.X ^ (3 * (k + 1)) - 1 =
            (Polynomial.X ^ (3 * k) - 1) * Polynomial.X ^ 3 +
              (Polynomial.X ^ 3 - 1) := by
                rw [Nat.mul_succ, pow_add]
                ring
        _ = M8.P3Family.polynomial *
            (q * Polynomial.X ^ 3 + (Polynomial.X - 1)) := by
              rw [hq]
              unfold M8.P3Family.polynomial
              ring
  have hone : (-1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    ext n
    by_cases hn : n = 0 <;>
      norm_num [Polynomial.coeff_neg, Polynomial.coeff_one, hn]
  simpa [M6.Cyclic.modulus, sub_eq_add_neg, hone] using h k
