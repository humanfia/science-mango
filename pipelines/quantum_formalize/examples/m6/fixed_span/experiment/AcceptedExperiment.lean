import M6FixedSpan

theorem M6.FixedSpan.distance_improvement : ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^3 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0) := by
  change ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^3 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)
  intro R
  have h := tendsto_pow_const_div_const_pow_of_one_lt 3 (r := (4 : ℝ)) (by norm_num)
  simpa only [zero_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h.mul_const ((4 : ℝ)^R)

theorem M6.FixedSpan.recipe_degree : M6.FixedSpan.recipe.Monic ∧ M6.FixedSpan.recipe.natDegree = 2 := by
  change M6.FixedSpan.recipe.Monic ∧ M6.FixedSpan.recipe.natDegree = 2
  unfold M6.FixedSpan.recipe
  constructor
  · monicity!
  · compute_degree!

theorem M6.FixedSpan.recipe_divides : ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N := by
  change ∀ N : ℕ, 3 ∣ N → M6.FixedSpan.recipe ∣ M6.Cyclic.modulus N
  intro N hN
  obtain ⟨k, rfl⟩ := hN
  have htwo : (2 : M6.Cyclic.BinaryPolynomial) = 0 :=
    CharP.cast_eq_zero M6.Cyclic.BinaryPolynomial 2
  have hneg : -(1 : M6.Cyclic.BinaryPolynomial) = 1 := by
    calc
      -(1 : M6.Cyclic.BinaryPolynomial) = -1 + 2 := by rw [htwo]; simp
      _ = 1 := by ring
  have hfactor : M6.FixedSpan.recipe ∣ (Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ 3 - 1 := by
    refine ⟨Polynomial.X + 1, ?_⟩
    symm
    calc
      M6.FixedSpan.recipe * (Polynomial.X + 1) =
          Polynomial.X ^ 3 + 1 + (2 : M6.Cyclic.BinaryPolynomial) *
            (Polynomial.X ^ 2 + Polynomial.X) := by
        unfold M6.FixedSpan.recipe
        ring
      _ = Polynomial.X ^ 3 - 1 := by
        rw [htwo]
        simp [sub_eq_add_neg, hneg]
  apply dvd_trans hfactor
  simpa [M6.Cyclic.modulus, pow_mul, sub_eq_add_neg, hneg] using
    (sub_dvd_pow_sub_pow ((Polynomial.X : M6.Cyclic.BinaryPolynomial) ^ 3) 1 k)

theorem M6.FixedSpan.recipe_support : M6.FixedSpan.recipe.support = {0,1,2} := by
  classical
  change M6.FixedSpan.recipe.support = {0, 1, 2}
  ext n
  by_cases h0 : n = 0 <;> by_cases h1 : n = 1 <;> by_cases h2 : n = 2 <;>
    simp_all [M6.FixedSpan.recipe, Polynomial.mem_support_iff,
      Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_X_pow, eq_comm]

theorem M6.FixedSpan.witness_improvement : ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^4 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0) := by
  change ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^4 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)
  intro R
  have h := tendsto_pow_const_div_const_pow_of_one_lt 4 (r := (4 : ℝ)) (by norm_num)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h.mul_const ((4 : ℝ)^R)

theorem M6.FixedSpan.recipe_signature : ∀ N : ℕ, 3 ∣ N → M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N) = M6.FixedSpan.recipe := by
  change ∀ N : ℕ, 3 ∣ N → M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N) = M6.FixedSpan.recipe
  intro N hN
  simp [M6.Cyclic.signature, EuclideanDomain.gcd_self, EuclideanDomain.gcd_eq_left, M6.FixedSpan.recipe_divides N hN]

theorem M6.FixedSpan.nontrivial_family : ∀ k : ℕ, let N := 3*(k+1); 2 < N ∧ M6.FixedSpan.recipe.support.card = 3 ∧ 0 ∈ M6.FixedSpan.recipe.support ∧ Nat.gcd N (M6.FixedSpan.recipe.support.gcd id) = 1 ∧ (M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N)).natDegree = 2 := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ k : ℕ, let N := 3*(k+1); 2 < N ∧ M6.FixedSpan.recipe.support.card = 3 ∧ 0 ∈ M6.FixedSpan.recipe.support ∧ Nat.gcd N (M6.FixedSpan.recipe.support.gcd id) = 1 ∧ (M6.Cyclic.signature M6.FixedSpan.recipe M6.FixedSpan.recipe (M6.Cyclic.modulus N)).natDegree = 2
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro k
  dsimp only
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [M6.FixedSpan.recipe_support]
    decide
  · rw [M6.FixedSpan.recipe_support]
    decide
  · rw [M6.FixedSpan.recipe_support]
    have hg : ({0, 1, 2} : Finset ℕ).gcd id = 1 := by decide
    rw [hg]
    simp
  · rw [M6.FixedSpan.recipe_signature (3 * (k + 1)) ⟨k + 1, rfl⟩]
    exact M6.FixedSpan.recipe_degree.2
#print axioms M6.FixedSpan.distance_improvement
#print axioms M6.FixedSpan.recipe_degree
#print axioms M6.FixedSpan.recipe_divides
#print axioms M6.FixedSpan.recipe_signature
#print axioms M6.FixedSpan.recipe_support
#print axioms M6.FixedSpan.nontrivial_family
#print axioms M6.FixedSpan.witness_improvement
