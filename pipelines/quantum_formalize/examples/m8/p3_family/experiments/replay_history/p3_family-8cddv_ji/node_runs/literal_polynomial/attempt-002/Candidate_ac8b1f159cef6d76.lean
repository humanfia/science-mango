import FrozenTarget_ac8b1f159cef6d76
theorem M8.P3Family.literal_polynomial : QuantumHarnessFrozenTarget := by
    intro N inst hN
    classical
    have h0 : (0 : ZMod N).val = 0 := by simp
    have h1 : (1 : ZMod N).val = 1 := by
      change ((1 : ℕ) : ZMod N).val = 1
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h2 : (2 : ZMod N).val = 2 := by
      change ((2 : ℕ) : ZMod N).val = 2
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have h01 : (0 : ZMod N) ≠ 1 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [h0, h1] at hv
      omega
    have h02 : (0 : ZMod N) ≠ 2 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [h0, h2] at hv
      omega
    have h12 : (1 : ZMod N) ≠ 2 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [h1, h2] at hv
      omega
    simp [M8.P3Family.support, M8.P3Family.polynomial,
      M7.Supports.polynomial, h0, h1, h2, h01, h02, h12,
      add_assoc, add_comm, add_left_comm] <;>
      ext k <;> simp [Polynomial.coeff_monomial]
