import M6Euclid

theorem M6.Euclid.binary_normalization : ∀ p : M6.Euclid.BP, (p ≠ 0 → p.Monic) ∧ normalize p = p := by
  change ∀ p : M6.Euclid.BP, (p ≠ 0 → p.Monic) ∧ normalize p = p
  intro p
  have hm : p ≠ 0 → p.Monic := by
    intro hp
    change p.leadingCoeff = 1
    have binary : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases binary p.leadingCoeff with h | h
    · exact False.elim (hp (Polynomial.leadingCoeff_eq_zero.mp h))
    · exact h
  refine ⟨hm, ?_⟩
  by_cases hp : p = 0
  · subst p
    simp
  · exact (hm hp).normalize_eq_self

theorem M6.Euclid.rank_order : ∀ p q : M6.Euclid.BP, (M6.Euclid.rank p < M6.Euclid.rank q ↔ p.degree < q.degree) ∧ (M6.Euclid.rank p ≤ M6.Euclid.rank q ↔ p.degree ≤ q.degree) := by
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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p
