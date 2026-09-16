import FrozenTarget_b902e75f35e868fd
theorem M8.AntipodalFamily.literal_polynomial : QuantumHarnessFrozenTarget := by
  classical
  intro N inst hN hEven
  have h0 : 0 < N := by omega
  have h1 : 1 < N := by omega
  have hh : N / 2 < N := by omega
  have hs : N / 2 + 1 < N := by omega
  have hv : ∀ k : ℕ, k < N → (k : ZMod N).val = k := by
    intro k hk
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have hn : ∀ a b : ℕ, a < N → b < N → a ≠ b → (a : ZMod N) ≠ (b : ZMod N) := by
    intro a b ha hb hab heq
    have he := congrArg (fun x : ZMod N => x.val) heq
    rw [hv a ha, hv b hb] at he
    exact hab he
  have h01 : (0 : ZMod N) ≠ 1 := by
    simpa only [Nat.cast_zero, Nat.cast_one] using hn 0 1 h0 h1 (by omega)
  have h0h : (0 : ZMod N) ≠ (N / 2 : ℕ) := by
    simpa only [Nat.cast_zero] using hn 0 (N / 2) h0 hh (by omega)
  have h0s : (0 : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
    simpa only [Nat.cast_zero] using hn 0 (N / 2 + 1) h0 hs (by omega)
  have h1h : (1 : ZMod N) ≠ (N / 2 : ℕ) := by
    simpa only [Nat.cast_one] using hn 1 (N / 2) h1 hh (by omega)
  have h1s : (1 : ZMod N) ≠ (N / 2 + 1 : ℕ) := by
    simpa only [Nat.cast_one] using hn 1 (N / 2 + 1) h1 hs (by omega)
  have hhs : (N / 2 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) :=
    hn (N / 2) (N / 2 + 1) hh hs (by omega)
  have v1 : (1 : ZMod N).val = 1 := by
    simpa only [Nat.cast_one] using hv 1 h1
  simp only [M7.Supports.polynomial, M8.AntipodalFamily.support,
    M8.AntipodalFamily.polynomial, Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_insert, Finset.mem_singleton, h01, h0h, h0s, h1h, h1s, hhs,
    false_or, not_false_eq_true, ZMod.val_zero, v1,
    hv (N / 2) hh, hv (N / 2 + 1) hs,
    ← Polynomial.X_pow_eq_monomial, pow_zero, pow_one, pow_succ]
  ring
