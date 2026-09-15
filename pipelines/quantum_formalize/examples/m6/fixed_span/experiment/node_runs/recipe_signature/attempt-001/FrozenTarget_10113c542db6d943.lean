import M6FixedSpan

theorem M6.FixedSpan.recipe_divides : ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N := by
  change ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N
  intro N hN
  obtain ⟨k, rfl⟩ := hN
  have htwo : (2 : M6.Cyclic.BinaryPolynomial) = 0 :=
    CharP.cast_eq_zero M6.Cyclic.BinaryPolynomial 2
  have hneg : -(1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    calc
      -(1 : M6.Cyclic.BinaryPolynomial) = -1 + 2 := by rw [htwo]; simp
      _ = 1 := by ring
  have hfactor : M6.FixedSpan.recipe ∣ (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ 3 - 1 := by
    refine ⟨Polynomial.X + 1, ?_⟩
    symm
    calc
      M6.FixedSpan.recipe * (Polynomial.X + 1) =
          Polynomial.X ^ 3 + 1 + (2 : M6.Cyclic.BinaryPolynomial) *
            (Polynomial.X ^ 2 + Polynomial.X) := by
        unfold M6.FixedSpan.recipe
        ring
      _ = Polynomial.X ^ 3 - 1 := by
        rw [htwo]
        simp [sub_eq_add_neg, hneg]
  apply dvd_trans hfactor
  simpa [M6.Cyclic.modulus, pow_mul, sub_eq_add_neg, hneg] using
    (sub_dvd_pow_sub_pow ((Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ 3) 1 k)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, 3 ∣ N → M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N) = M6.FixedSpan.recipe
