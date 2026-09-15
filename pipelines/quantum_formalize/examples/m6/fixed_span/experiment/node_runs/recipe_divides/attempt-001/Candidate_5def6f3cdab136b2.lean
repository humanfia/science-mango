import FrozenTarget_5def6f3cdab136b2
theorem M6.FixedSpan.recipe_divides : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N
  intro N hN
  rcases hN with ⟨k, rfl⟩
  have htwo : (2 : Polynomial (ZMod 2)) = 0 := by
    change Polynomial.C (2 : ZMod 2) = 0
    norm_num
  have hb : (Polynomial.X : Polynomial (ZMod 2)) ^ 3 - 1 =
      M6.FixedSpan.recipe * (Polynomial.X + 1) := by
    change Polynomial.X ^ 3 - 1 =
      (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial (ZMod 2)) * (Polynomial.X + 1)
    calc
      Polynomial.X ^ 3 - 1 =
          (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial (ZMod 2)) * (Polynomial.X + 1) -
            2 * (Polynomial.X + Polynomial.X ^ 2 + 1) := by ring
      _ = _ := by rw [htwo]; simp
  change M6.FixedSpan.recipe ∣ (Polynomial.X : Polynomial (ZMod 2)) ^ (3 * k) - 1
  induction k with
  | zero => simp
  | succ k ih =>
    rcases ih with ⟨q, hq⟩
    refine ⟨q * Polynomial.X ^ 3 + (Polynomial.X + 1), ?_⟩
    calc
      (Polynomial.X : Polynomial (ZMod 2)) ^ (3 * (k + 1)) - 1 =
          (Polynomial.X ^ (3 * k) - 1) * Polynomial.X ^ 3 + (Polynomial.X ^ 3 - 1) := by
        rw [Nat.mul_succ, pow_add]
        ring
      _ = M6.FixedSpan.recipe * (q * Polynomial.X ^ 3 + (Polynomial.X + 1)) := by
        rw [hq, hb]
        ring
