import FrozenTarget_cabc94584fa43787
theorem M8.P3Family.literal_polynomial : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → M7.Supports.polynomial (M8.P3Family.support N) = M8.P3Family.polynomial
  intro N inst hN
  classical
  have hv (k : ℕ) (hk : k < N) : (k : ZMod N).val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have h0 : (0 : ZMod N).val = 0 := by simp
  have h1 : (1 : ZMod N).val = 1 := by
    simpa using hv 1 (by omega)
  have h2 : (2 : ZMod N).val = 2 := by
    simpa using hv 2 (by omega)
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have := congrArg ZMod.val h
    omega
  have h02 : (0 : ZMod N) ≠ 2 := by
    intro h
    have := congrArg ZMod.val h
    omega
  have h12 : (1 : ZMod N) ≠ 2 := by
    intro h
    have := congrArg ZMod.val h
    omega
  simp [M8.P3Family.support, M8.P3Family.polynomial,
    M7.Supports.polynomial, M7.Supports.natSupport,
    h0, h1, h2, h01, h02, h12, Polynomial.monomial_eq_C_mul_X,
    add_assoc, add_comm, add_left_comm]
