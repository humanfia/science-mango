import FrozenTarget_815051fcce0a863a
theorem M8.P4Gcd.factorization : QuantumHarnessFrozenTarget := by
  intro m
  have htwo : (2 : M6.Cyclic.BinaryPolynomial) = 0 := by
    change Polynomial.C (2 : ZMod 2) = 0
    norm_num
  have hneg : -(1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    apply neg_eq_iff_add_eq_zero.mpr
    simpa only [one_add_one_eq_two] using htwo
  have hsquare : (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial)^2 = Polynomial.X^2 - 1 := by
    calc
      (Polynomial.X + 1 : M6.Cyclic.BinaryPolynomial)^2 =
          Polynomial.X^2 - 1 + 2 * (Polynomial.X + 1) := by ring
      _ = Polynomial.X^2 - 1 := by rw [htwo]; ring
  have hgeom : ∀ n : ℕ,
      (Polynomial.X^2 - 1 : M6.Cyclic.BinaryPolynomial) *
        (Finset.range n).sum (fun i => Polynomial.X^(2*i)) =
          Polynomial.X^(2*n) - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      simp only [Nat.mul_succ, pow_add]
      ring
  have hexp : 2 * (2*m+1) = 4*m+2 := by omega
  simpa [M6.Cyclic.modulus, M8.P4Gcd.oddCofactor, hsquare, hexp,
    sub_eq_add_neg, hneg] using (hgeom (2*m+1)).symm
