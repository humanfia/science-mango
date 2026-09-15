import FrozenTarget_64ce421e39c64ac9
theorem M6.Euclid.rank_order : QuantumHarnessFrozenTarget := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.rank p < M6.Euclid.rank q ↔ p.degree < q.degree) ∧ (M6.Euclid.rank p ≤ M6.Euclid.rank q ↔ p.degree ≤ q.degree)
  intro p q
  by_cases hp : p = 0 <;> by_cases hq : q = 0
  · subst p
    subst q
    simp [M6.Euclid.rank]
  · subst p
    simp [M6.Euclid.rank, hq, Polynomial.degree_eq_natDegree hq]
  · subst q
    simp [M6.Euclid.rank, hp, Polynomial.degree_eq_natDegree hp]
  · simp [M6.Euclid.rank, hp, hq, Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq]
