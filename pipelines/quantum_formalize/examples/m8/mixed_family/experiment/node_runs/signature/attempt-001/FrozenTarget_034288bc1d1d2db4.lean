import M8MixedFamily

theorem M8.MixedFamily.algebra : M8.MixedFamily.b = M8.MixedFamily.a^2 ∧ M8.MixedFamily.a*M8.MixedFamily.b = 1+Polynomial.X+Polynomial.X^2+Polynomial.X^3 := by
  change (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) = (1 + Polynomial.X) ^ 2 ∧
    (1 + Polynomial.X : Polynomial (ZMod 2)) * (1 + Polynomial.X ^ 2) =
      1 + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3
  have h : (1 + 1 : Polynomial (ZMod 2)) = 0 := by
    simpa only [map_add, map_one, map_zero] using
      congrArg (fun c : ZMod 2 => Polynomial.C c)
        (show (1 + 1 : ZMod 2) = 0 by decide)
  constructor
  · calc
      (1 + Polynomial.X ^ 2 : Polynomial (ZMod 2)) =
          1 + Polynomial.X ^ 2 + (1 + 1) * Polynomial.X := by rw [h]; simp
      _ = (1 + Polynomial.X) ^ 2 := by ring
  · ring

theorem M8.MixedFamily.literal_polynomials : ∀ (N : ℕ) [NeZero N], 7 ≤ N → M7.Supports.polynomial (M8.MixedFamily.left N) = M8.MixedFamily.a ∧ M7.Supports.polynomial (M8.MixedFamily.right N) = M8.MixedFamily.b := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 7 ≤ N → M7.RecipeSignature.signature (M8.MixedFamily.recipe N) = M8.MixedFamily.a
