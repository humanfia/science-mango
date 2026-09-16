import FrozenTarget_e83479788166f0cb
theorem M8.AntipodalFamily.literal_polynomial : QuantumHarnessFrozenTarget := by
    change ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M7.Supports.polynomial (M8.AntipodalFamily.support N) = M8.AntipodalFamily.polynomial N
    intro N inst hN hEven
    classical
    have hh : N / 2 < N := by omega
    have hs : N / 2 + 1 < N := by omega
    have hv (a : ℕ) (ha : a < N) : (a : ZMod N).val = a := by
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
    have hn (a b : ℕ) (ha : a < N) (hb : b < N) (hab : a ≠ b) :
        (a : ZMod N) ≠ (b : ZMod N) := by
      intro he
      have he' := congrArg ZMod.val he
      rw [hv a ha, hv b hb] at he'
      exact hab he'
    have h01 : (0 : ZMod N) ≠ 1 := by
      simpa only [Nat.cast_zero, Nat.cast_one] using hn 0 1 (by omega) (by omega) (by omega)
    have h0h : (0 : ZMod N) ≠ ((N / 2 : ℕ) : ZMod N) := by
      simpa only [Nat.cast_zero] using hn 0 (N / 2) (by omega) hh (by omega)
    have h0s : (0 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
      simpa only [Nat.cast_zero] using hn 0 (N / 2 + 1) (by omega) hs (by omega)
    have h1h : (1 : ZMod N) ≠ ((N / 2 : ℕ) : ZMod N) := by
      simpa only [Nat.cast_one] using hn 1 (N / 2) (by omega) hh (by omega)
    have h1s : (1 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
      simpa only [Nat.cast_one] using hn 1 (N / 2 + 1) (by omega) hs (by omega)
    have hhs : ((N / 2 : ℕ) : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) :=
      hn (N / 2) (N / 2 + 1) hh hs (by omega)
    have v0 : (0 : ZMod N).val = 0 := by
      simpa only [Nat.cast_zero] using hv 0 (by omega)
    have v1 : (1 : ZMod N).val = 1 := by
      simpa only [Nat.cast_one] using hv 1 (by omega)
    have hn0 : N / 2 ≠ 0 := by omega
    have hn1 : N / 2 ≠ 1 := by omega
    have hsn0 : N / 2 + 1 ≠ 0 := by omega
    have hsn1 : N / 2 + 1 ≠ 1 := by omega
    simp [M7.Supports.polynomial, M7.Supports.natSupport,
      M8.AntipodalFamily.support, M8.AntipodalFamily.polynomial,
      h01, h0h, h0s, h1h, h1s, hhs, v0, v1, hv (N / 2) hh,
      hv (N / 2 + 1) hs, hn0, hn1, hsn0, hsn1,
      Ne.symm hn0, Ne.symm hn1, Ne.symm hsn0, Ne.symm hsn1,
      Polynomial.monomial_eq_C_mul_X, pow_succ] <;> ring
