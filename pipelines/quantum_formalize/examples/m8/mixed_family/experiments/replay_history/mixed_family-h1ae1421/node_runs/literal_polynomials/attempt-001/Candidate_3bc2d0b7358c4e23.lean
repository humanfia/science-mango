import FrozenTarget_3bc2d0b7358c4e23
theorem M8.MixedFamily.literal_polynomials : QuantumHarnessFrozenTarget := by
    classical
    intro N inst hN
    have h1 : (1 : ZMod N).val = 1 := by
      change ((1 : ℕ) : ZMod N).val = 1
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 1 < N)]
    have h2 : (2 : ZMod N).val = 2 := by
      change ((2 : ℕ) : ZMod N).val = 2
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 2 < N)]
    have h01 : (0 : ZMod N) ≠ 1 := by
      intro h
      have := congrArg ZMod.val h
      simp [h1] at this
    have h02 : (0 : ZMod N) ≠ 2 := by
      intro h
      have := congrArg ZMod.val h
      simp [h2] at this
    constructor <;>
      simp [M8.MixedFamily.left, M8.MixedFamily.right,
        M8.MixedFamily.a, M8.MixedFamily.b,
        M7.Supports.polynomial, M7.Supports.natSupport,
        h01, h02, h1, h2, Polynomial.monomial_eq_C_mul_X]
