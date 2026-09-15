import M6TransferScatter

theorem M6.Transfer.scatter_prefix_formula : ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input initial : M6.Transfer.CoefficientArray R N) (l : List (M6.Transfer.ScatterEvent R N)) (addr : M6.Transfer.CoefficientAddress R N), (l.foldl (M6.Transfer.scatterUpdate W input) initial) addr = initial addr + (l.map (fun e => if M6.Transfer.eventDestination e = some addr then M6.Transfer.eventTerm W input e else 0)).sum := by
  classical
  intro R N W input initial l addr
  induction l generalizing initial with
  | nil => simp
  | cons e l ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      cases h : M6.Transfer.eventDestination e with
      | none =>
          simp [M6.Transfer.scatterUpdate, h]
      | some a =>
          by_cases ha : a = addr
          · subst a
            simp [M6.Transfer.scatterUpdate, h, add_assoc]
          · simp [M6.Transfer.scatterUpdate, h, Function.update_apply, ha, Ne.symm ha]

theorem M6.Transfer.small_polynomial_convolution : ∀ (p q : Polynomial ℤ) (d : ℕ), q.natDegree ≤ 2 → (p*q).coeff d = ∑ e : Fin 3, if e.val ≤ d then p.coeff (d-e.val) * q.coeff e.val else 0 := by
  change ∀ (p q : Polynomial ℤ) (d : ℕ), q.natDegree ≤ 2 → _
  intro p q d hqdeg
  have hq : q = Polynomial.monomial 0 (q.coeff 0) +
      Polynomial.monomial 1 (q.coeff 1) +
      Polynomial.monomial 2 (q.coeff 2) := by
    ext n
    by_cases hn : n ≤ 2
    · interval_cases n <;>
        simp only [Polynomial.coeff_add, Polynomial.coeff_monomial] <;> norm_num
    · have hz : q.coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have h0 : 0 ≠ n := by omega
      have h1 : 1 ≠ n := by omega
      have h2 : 2 ≠ n := by omega
      simp only [Polynomial.coeff_add, Polynomial.coeff_monomial,
        if_neg h0, if_neg h1, if_neg h2, hz, add_zero]
  have hm : ∀ (n : ℕ) (r : ℤ),
      (p * Polynomial.monomial n r).coeff d =
        if n ≤ d then p.coeff (d - n) * r else 0 := by
    intro n r
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc,
      Polynomial.coeff_mul_X_pow']
    split_ifs <;> simp [Polynomial.coeff_mul_C]
  conv_lhs => rw [hq]
  simp only [mul_add, Polynomial.coeff_add, hm]
  have h1 : (1 ≤ d) ↔ (0 < d) := by omega
  have h2 : (2 ≤ d) ↔ (1 < d) := by omega
  simp [Fin.sum_univ_succ, h1, h2, add_assoc]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (v : M6.Transfer.Memory R → Polynomial ℤ) (addr : M6.Transfer.CoefficientAddress R N), (∀ m t, (W m t).natDegree ≤ 2) → M6.Transfer.scatterLayer W (M6.Transfer.encodeCoefficients v) addr = (M6.Transfer.propagate W v addr.1).coeff addr.2.val
