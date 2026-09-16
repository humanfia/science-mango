import FrozenTarget_337c9d3bdec9fd13
theorem M8.AntipodalFamily.literal_polynomial : QuantumHarnessFrozenTarget := by
  classical
  intro N inst hN hEven
  have hhalf : 1 < N / 2 := by omega
  have hlt : N / 2 + 1 < N := by omega
  have hv (k : ℕ) (hk : k < N) : (k : ZMod N).val = k := by
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have v0 : (0 : ZMod N).val = 0 := by simp
  have v1 : (1 : ZMod N).val = 1 := by
    simpa using hv 1 (by omega)
  have vh : ((N / 2 : ℕ) : ZMod N).val = N / 2 := hv _ (by omega)
  have vs : ((N / 2 + 1 : ℕ) : ZMod N).val = N / 2 + 1 := hv _ hlt
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, v1] at hh
    omega
  have h0h : (0 : ZMod N) ≠ ((N / 2 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, vh] at hh
    omega
  have h0s : (0 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v0, vs] at hh
    omega
  have h1h : (1 : ZMod N) ≠ ((N / 2 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v1, vh] at hh
    omega
  have h1s : (1 : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [v1, vs] at hh
    omega
  have hhs : ((N / 2 : ℕ) : ZMod N) ≠ ((N / 2 + 1 : ℕ) : ZMod N) := by
    intro h
    have hh := congrArg ZMod.val h
    rw [vh, vs] at hh
    omega
  have hn0 : N / 2 ≠ 0 := by omega
  have hn1 : N / 2 ≠ 1 := by omega
  have hs0 : N / 2 + 1 ≠ 0 := by omega
  have hs1 : N / 2 + 1 ≠ 1 := by omega
  simp [M7.Supports.polynomial, M7.Supports.natSupport,
    M8.AntipodalFamily.support, M8.AntipodalFamily.polynomial,
    h01, h0h, h0s, h1h, h1s, hhs, Ne.symm h01,
    Ne.symm h0h, Ne.symm h0s, Ne.symm h1h, Ne.symm h1s,
    Ne.symm hhs, v0, v1, vh, vs, hn0, hn1, hs0, hs1,
    Ne.symm hn0, Ne.symm hn1, Ne.symm hs0, Ne.symm hs1,
    Polynomial.monomial_eq_C_mul_X, pow_succ] <;> ring
