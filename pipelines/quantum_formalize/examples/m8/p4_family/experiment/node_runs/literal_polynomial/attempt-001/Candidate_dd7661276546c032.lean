import FrozenTarget_dd7661276546c032
theorem M8.P4Family.literal_polynomial : QuantumHarnessFrozenTarget := by
    intro N inst hN
    classical
    have h0 : (0 : ZMod N).val = 0 := by simp
    have h1 : (1 : ZMod N).val = 1 := by
      change ((1 : ℕ) : ZMod N).val = 1
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h2 : (2 : ZMod N).val = 2 := by
      change ((2 : ℕ) : ZMod N).val = 2
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h3 : (3 : ZMod N).val = 3 := by
      change ((3 : ℕ) : ZMod N).val = 3
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h01 : (0 : ZMod N) ≠ 1 := by
      intro h
      have := congrArg ZMod.val h
      omega
    have h02 : (0 : ZMod N) ≠ 2 := by
      intro h
      have := congrArg ZMod.val h
      omega
    have h03 : (0 : ZMod N) ≠ 3 := by
      intro h
      have := congrArg ZMod.val h
      omega
    have h12 : (1 : ZMod N) ≠ 2 := by
      intro h
      have := congrArg ZMod.val h
      omega
    have h13 : (1 : ZMod N) ≠ 3 := by
      intro h
      have := congrArg ZMod.val h
      omega
    have h23 : (2 : ZMod N) ≠ 3 := by
      intro h
      have := congrArg ZMod.val h
      omega
    simp [M8.P4Family.support, M7.Supports.polynomial,
      M7.Supports.natSupport, M8.P4Family.polynomial,
      h0, h1, h2, h3, h01, h02, h03, h12, h13, h23,
      Polynomial.monomial_eq_C_mul_X, add_assoc, add_comm, add_left_comm]
