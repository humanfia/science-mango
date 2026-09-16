import FrozenTarget_f6eb951bcaeae11b
theorem M8.AntipodalFamily.polynomial_power : QuantumHarnessFrozenTarget := by
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
