import M8P3Family

theorem M8.P3Family.divides_modulus : ∀ N : ℕ, 3 ∣ N → M8.P3Family.polynomial ∣ M6.Cyclic.modulus N := by
  change ∀ N : ℕ, 3 ∣ N → M8.P3Family.polynomial ∣ M6.Cyclic.modulus N
  intro N hN
  obtain ⟨k, rfl⟩ := hN
  have h : ∀ k : ℕ, M8.P3Family.polynomial ∣
      (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ (3 * k) - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨q * Polynomial.X ^ 3 + (Polynomial.X - 1), ?_⟩
      calc
        Polynomial.X ^ (3 * (k + 1)) - 1 =
            (Polynomial.X ^ (3 * k) - 1) * Polynomial.X ^ 3 +
              (Polynomial.X ^ 3 - 1) := by
                rw [Nat.mul_succ, pow_add]
                ring
        _ = M8.P3Family.polynomial *
            (q * Polynomial.X ^ 3 + (Polynomial.X - 1)) := by
              rw [hq]
              unfold M8.P3Family.polynomial
              ring
  have hone : (-1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    ext n
    by_cases hn : n = 0 <;>
      norm_num [Polynomial.coeff_neg, Polynomial.coeff_one, hn]
  simpa [M6.Cyclic.modulus, sub_eq_add_neg, hone] using h k

theorem M8.P3Family.literal_polynomial : ∀ (N : ℕ) [NeZero N], 3 ≤ N → M7.Supports.polynomial (M8.P3Family.support N) = M8.P3Family.polynomial := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → M7.Supports.polynomial (M8.P3Family.support N) = M8.P3Family.polynomial
  intro N inst hN
  classical
  have h0 : (0 : ZMod N).val = 0 := by simp
  have h1 : (1 : ZMod N).val = 1 := by
    have h : ((1 : ℕ) : ZMod N).val = 1 % N := by
      rw [ZMod.val_natCast]
    simpa only [Nat.cast_one, Nat.mod_eq_of_lt (show 1 < N by omega)] using h
  have h2 : (2 : ZMod N).val = 2 := by
    have h : ((2 : ℕ) : ZMod N).val = 2 % N := by
      rw [ZMod.val_natCast]
    simpa only [Nat.cast_ofNat, Nat.mod_eq_of_lt (show 2 < N by omega)] using h
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
  simp [M8.P3Family.support, M8.P3Family.polynomial, M7.Supports.polynomial,
    h0, h1, h2, h01, h02, h12, add_assoc, add_comm, add_left_comm]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M7.RecipeSignature.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial
