import FrozenTarget_b6bf50202c54f753
theorem M8.AntipodalFamily.literal_polynomial : QuantumHarnessFrozenTarget := by
  classical
  intro N inst hN hEven
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  have hh : N / 2 < N := by omega
  have hs : N / 2 + 1 < N := by omega
  have hv : ∀ k : ℕ, k < N → (k : ZMod N).val = k := by
    intro k hk
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have hn : ∀ a b : ℕ, a < N → b < N → a ≠ b → (a : ZMod N) ≠ (b : ZMod N) := by
    intro a b ha hb hab he
    have he' := congrArg (fun z : ZMod N => z.val) he
    rw [hv a ha, hv b hb] at he'
    exact hab he'
  have h01 : (0 : ZMod N) ≠ 1 := by
    exact hn 0 1 h0 h1 (by omega)
  have h0h : (0 : ZMod N) ≠ (N / 2 : ℕ) := by
    exact hn 0 (N / 2) h0 hh (by omega)
  have h0s : (0 : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
    exact hn 0 (N / 2 + 1) h0 hs (by omega)
  have h1h : (1 : ZMod N) ≠ (N / 2 : ℕ) := by
    exact hn 1 (N / 2) h1 hh (by omega)
  have h1s : (1 : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
    exact hn 1 (N / 2 + 1) h1 hs (by omega)
  have hhs : ((N / 2 : ℕ) : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
    exact hn (N / 2) (N / 2 + 1) hh hs (by omega)
  have v1 : (1 : ZMod N).val = 1 := by
    simpa using hv 1 h1
  simp [M7.Supports.polynomial, M7.Supports.natSupport,
    M8.AntipodalFamily.support, M8.AntipodalFamily.polynomial,
    h01, h0h, h0s, h1h, h1s, hhs, v1, hv (N / 2) hh,
    hv (N / 2 + 1) hs, ← Polynomial.X_pow_eq_monomial,
    pow_succ, Nat.ne_of_lt (show 1 < N / 2 by omega),
    Nat.ne_of_lt (show 0 < N / 2 by omega)] <;> ring
