import M8P4Gcd

theorem M8.P4Gcd.cofactor_eval : ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1 := by
  change ∀ m : ℕ, Polynomial.eval 1 (M8.P4Gcd.oddCofactor m) = 1
  intro m
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [M8.P4Gcd.oddCofactor, Polynomial.eval_finset_sum, Nat.cast_add, Nat.cast_mul, htwo]

theorem M8.P4Gcd.factorization : ∀ m : ℕ, M6.Cyclic.modulus (4*m+2) = (Polynomial.X+1)^2 * M8.P4Gcd.oddCofactor m := by
  intro m
  have htwo : (2 : M6.Cyclic.BinaryPolynomial) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (Polynomial.C : ZMod 2 → Polynomial (ZMod 2))
        (show (2 : ZMod 2) = 0 by decide)
  have hneg : -(1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    linear_combination -htwo
  have hsquare : ((Polynomial.X : M6.Cyclic.BinaryPolynomial) + 1)^2 = Polynomial.X^2 - 1 := by
    linear_combination (Polynomial.X + 1) * htwo
  have hgeom : ∀ n : ℕ,
      ((Polynomial.X : M6.Cyclic.BinaryPolynomial)^2 - 1) *
        (Finset.range n).sum (fun i => Polynomial.X^(2*i)) =
          Polynomial.X^(2*n) - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      rw [Nat.mul_succ, pow_add]
      ring
  have hexp : 2 * (2*m+1) = 4*m+2 := by omega
  simpa [M6.Cyclic.modulus, M8.P4Gcd.oddCofactor, hsquare,
    hexp, sub_eq_add_neg, hneg] using (hgeom (2*m+1)).symm

theorem M8.P4Gcd.cofactor_coprime : ∀ m : ℕ, IsCoprime (Polynomial.X+1) (M8.P4Gcd.oddCofactor m) := by
  change ∀ m : ℕ, IsCoprime (Polynomial.X + 1) (M8.P4Gcd.oddCofactor m)
  intro m
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have hr : Polynomial.IsRoot (M8.P4Gcd.oddCofactor m - 1) (-1 : ZMod 2) := by
    change Polynomial.eval (-1) (M8.P4Gcd.oddCofactor m - 1) = 0
    rw [hneg]
    simp [M8.P4Gcd.cofactor_eval]
  have hd : Polynomial.X + 1 ∣ M8.P4Gcd.oddCofactor m - 1 := by
    simpa only [map_neg, map_one, sub_neg_eq_add] using
      (Polynomial.dvd_iff_isRoot.mpr hr)
  rcases hd with ⟨q, hq⟩
  refine ⟨-q, 1, ?_⟩
  calc
    -q * (Polynomial.X + 1) + 1 * M8.P4Gcd.oddCofactor m =
        M8.P4Gcd.oddCofactor m - (Polynomial.X + 1) * q := by ring
    _ = 1 := by rw [← hq]; ring
def QuantumHarnessFrozenTarget : Prop :=
  ∀ m : ℕ, gcd M8.P4Family.polynomial (M6.Cyclic.modulus (4*m+2)) = (Polynomial.X+1)^2
