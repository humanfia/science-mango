import FrozenTarget_46d01fefa514f457
theorem M6.FixedSpan.recipe_divides : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N
  intro N hN
  rcases hN with ⟨k, rfl⟩
  have htwo : (2 : M6.Cyclic.BinaryPolynomial) = 0 :=
    CharP.cast_eq_zero M6.Cyclic.BinaryPolynomial 2
  have hneg : (-1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    calc
      -1 = -1 + 2 := by rw [htwo, add_zero]
      _ = 1 := by ring
  have hf : M6.FixedSpan.recipe ∣ (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ 3 - 1 := by
    refine ⟨Polynomial.X + 1, ?_⟩
    unfold M6.FixedSpan.recipe
    rw [sub_eq_add_neg, hneg]
    ring_nf <;> simp [htwo]
  have hp : ∀ j : ℕ, M6.FixedSpan.recipe ∣ ((Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ 3) ^ j - 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rcases ih with ⟨q, hq⟩
      rcases hf with ⟨r, hr⟩
      refine ⟨q * Polynomial.X ^ 3 + r, ?_⟩
      rw [pow_succ]
      calc
        (Polynomial.X ^ 3) ^ j * Polynomial.X ^ 3 - 1 =
            ((Polynomial.X ^ 3) ^ j - 1) * Polynomial.X ^ 3 + (Polynomial.X ^ 3 - 1) := by ring
        _ = M6.FixedSpan.recipe * (q * Polynomial.X ^ 3 + r) := by
          rw [hq, hr]
          ring
  simpa [M6.Cyclic.modulus, pow_mul, sub_eq_add_neg, hneg] using hp k
