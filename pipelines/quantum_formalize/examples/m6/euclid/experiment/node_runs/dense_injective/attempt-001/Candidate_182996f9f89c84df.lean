import FrozenTarget_182996f9f89c84df
theorem M6.Euclid.dense_injective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ N + 1 → M6.Euclid.rank q ≤ N + 1 → M6.Euclid.dense N p = M6.Euclid.dense N q → p = q
  intro N p q hp hq hd
  classical
  apply Polynomial.ext
  intro i
  by_cases hi : i < N + 1
  · change List.ofFn (fun j : Fin (N + 1) => p.coeff j) = List.ofFn (fun j : Fin (N + 1) => q.coeff j) at hd
    have he : (List.ofFn (fun j : Fin (N + 1) => p.coeff j))[i]'(by simpa using hi) = (List.ofFn (fun j : Fin (N + 1) => q.coeff j))[i]'(by simpa using hi) := by
      congr 1
    simpa only [List.getElem_ofFn] using he
  · have hpz : p.coeff i = 0 := by
      by_cases hp0 : p = 0
      · simp [hp0]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simp [M6.Euclid.rank, hp0] at hp
        omega
    have hqz : q.coeff i = 0 := by
      by_cases hq0 : q = 0
      · simp [hq0]
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simp [M6.Euclid.rank, hq0] at hq
        omega
    exact hpz.trans hqz.symm
