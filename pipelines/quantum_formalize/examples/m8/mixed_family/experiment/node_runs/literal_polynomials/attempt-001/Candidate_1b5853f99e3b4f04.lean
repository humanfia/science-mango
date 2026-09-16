import FrozenTarget_1b5853f99e3b4f04
theorem M8.MixedFamily.literal_polynomials : QuantumHarnessFrozenTarget := by
  intro N inst hN
  classical
  have hv (k : ℕ) (hk : k < N) : (k : ZMod N).val = k := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  have h1 : (1 : ZMod N).val = 1 := by
    simpa only [Nat.cast_one] using hv 1 (by omega)
  have h2 : (2 : ZMod N).val = 2 := by
    simpa using hv 2 (by omega)
  have h01 : (0 : ZMod N) ≠ 1 := by
    intro h
    have hh := congrArg ZMod.val h
    simp [h1] at hh
  have h02 : (0 : ZMod N) ≠ 2 := by
    intro h
    have hh := congrArg ZMod.val h
    simp [h2] at hh
  constructor <;>
    simp [M8.MixedFamily.left, M8.MixedFamily.right,
      M8.MixedFamily.a, M8.MixedFamily.b, M7.Supports.polynomial,
      h01, h02, h1, h2] <;>
    ext k <;>
    simp [Polynomial.coeff_X, Polynomial.coeff_X_pow, eq_comm]
