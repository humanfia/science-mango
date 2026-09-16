import FrozenTarget_e5e5a2581cfa02fc
theorem M8.AntipodalFamily.literal_polynomial : QuantumHarnessFrozenTarget := by
    classical
    intro N inst hN hEven
    have hh : N / 2 < N := by omega
    have hs : N / 2 + 1 < N := by omega
    have hv : ∀ a : ℕ, a < N → (a : ZMod N).val = a := by
      intro a ha
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
    have hn : ∀ a b : ℕ, a < N → b < N → a ≠ b → (a : ZMod N) ≠ (b : ZMod N) := by
      intro a b ha hb hab he
      apply hab
      have he' := congrArg (fun z : ZMod N => z.val) he
      simpa only [hv a ha, hv b hb] using he'
    have h01 : (0 : ZMod N) ≠ 1 := by
      simpa only [Nat.cast_zero, Nat.cast_one] using hn 0 1 (by omega) (by omega) (by omega)
    have h0h : (0 : ZMod N) ≠ (N / 2 : ℕ) := by
      simpa only [Nat.cast_zero] using hn 0 (N / 2) (by omega) hh (by omega)
    have h0s : (0 : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
      simpa only [Nat.cast_zero] using hn 0 (N / 2 + 1) (by omega) hs (by omega)
    have h1h : (1 : ZMod N) ≠ (N / 2 : ℕ) := by
      simpa only [Nat.cast_one] using hn 1 (N / 2) (by omega) hh (by omega)
    have h1s : (1 : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
      simpa only [Nat.cast_one] using hn 1 (N / 2 + 1) (by omega) hs (by omega)
    have hhs : ((N / 2 : ℕ) : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) :=
      hn (N / 2) (N / 2 + 1) hh hs (by omega)
    have v0 : (0 : ZMod N).val = 0 := by
      simpa only [Nat.cast_zero] using hv 0 (by omega)
    have v1 : (1 : ZMod N).val = 1 := by
      simpa only [Nat.cast_one] using hv 1 (by omega)
    unfold M7.Supports.polynomial M8.AntipodalFamily.support M8.AntipodalFamily.polynomial
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      h01, h0h, h0s, h1h, h1s, hhs, false_or, or_false, not_false_eq,
      Finset.sum_singleton]
    simp only [v0, v1, hv (N / 2) hh, hv (N / 2 + 1) hs,
      ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_1, one_mul,
      pow_zero, pow_one, pow_succ]
    ring
