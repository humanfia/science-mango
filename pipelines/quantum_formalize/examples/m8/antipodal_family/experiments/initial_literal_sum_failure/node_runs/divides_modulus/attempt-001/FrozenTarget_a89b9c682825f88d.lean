import M8AntipodalFamily

theorem M8.AntipodalFamily.modulus_power : ∀ (v : ℕ), 3 ≤ v → M6.Cyclic.modulus (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^v) := by
  change ∀ (v : ℕ), 3 ≤ v → M6.Cyclic.modulus (2^v) = (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial)^(2^v)
  intro v hv
  simp [M6.Cyclic.modulus, add_pow_char_pow]

theorem M8.AntipodalFamily.polynomial_power : ∀ (v : ℕ), 3 ≤ v → M8.AntipodalFamily.polynomial (2^v) = (Polynomial.X+1 : M6.Cyclic.BinaryPolynomial)^(2^(v-1)+1) := by
  intro v hv
  change (1 + Polynomial.X) * (1 + Polynomial.X ^ (2 ^ v / 2)) =
    (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial) ^ (2 ^ (v - 1) + 1)
  have hd : 2 ^ v / 2 = 2 ^ (v - 1) := by
    calc
      2 ^ v / 2 = (2 ^ (v - 1) * 2) / 2 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ v)]
      _ = 2 ^ (v - 1) := by simp
  have hf : (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial) ^ (2 ^ (v - 1)) =
      Polynomial.X ^ (2 ^ (v - 1)) + 1 := by
    simpa using (add_pow_char_pow (Polynomial.X : M6.Cyclic.BinaryPolynomial) 1 2 (v - 1))
  rw [hd, pow_succ, hf]
  ring
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (v : ℕ), 3 ≤ v → M8.AntipodalFamily.polynomial (2^v) ∣ M6.Cyclic.modulus (2^v)
