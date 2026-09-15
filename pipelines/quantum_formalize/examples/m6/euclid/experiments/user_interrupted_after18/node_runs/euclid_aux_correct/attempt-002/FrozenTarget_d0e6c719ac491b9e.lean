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

theorem M6.Euclid.cancel_mod : ∀ p q : M6.Euclid.BP, M6.Euclid.cancel p q % q = p % q := by
  change ∀ p q : M6.Euclid.BP, M6.Euclid.cancel p q % q = p % q
  intro p q
  apply Polynomial.mod_eq_of_dvd_sub
  simp [M6.Euclid.cancel, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

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

theorem M6.Euclid.cancel_drop : ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p := by
  change ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p
  intro p q hp hq hdeg
  apply ((M6.Euclid.rank_order (M6.Euclid.cancel p q) p).1).mpr
  have hmp := (M6.Euclid.binary_normalization p).1 hp
  have hmq := (M6.Euclid.binary_normalization q).1 hq
  simpa [M6.Euclid.cancel, hmp.leadingCoeff, mul_comm, mul_left_comm, mul_assoc] using
    (Polynomial.div_wf_lemma (p := p) (q := q) ⟨hdeg, hp⟩ hmq)

theorem M6.Euclid.remainder_aux_correct : ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ fuel → (M6.Euclid.remainderAux fuel p q).value = p % q ∧ (M6.Euclid.remainderAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.remainderAux fuel p q).value ≤ M6.Euclid.rank p := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ fuel → (M6.Euclid.remainderAux fuel p q).value = p % q ∧ (M6.Euclid.remainderAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.remainderAux fuel p q).value ≤ M6.Euclid.rank p
  intro fuel
  induction fuel with
  | zero =>
      intro p q hf
      have hp : p = 0 := by
        by_contra hp
        simp [M6.Euclid.rank, hp] at hf
      subst p
      simp [M6.Euclid.remainderAux, M6.Euclid.rank]
  | succ fuel ih =>
      intro p q hf
      by_cases hp : p = 0
      · subst p
        simp [M6.Euclid.remainderAux, M6.Euclid.rank]
      by_cases hq : q = 0
      · subst q
        simp [M6.Euclid.remainderAux]
      by_cases hd : p.degree < q.degree
      · have hm : p % q = p := (Polynomial.mod_eq_self_iff hq).2 hd
        simp [M6.Euclid.remainderAux, hp, hq, hd, hm]
      · have hle : q.degree ≤ p.degree := le_of_not_gt hd
        have hdrop := M6.Euclid.cancel_drop p q hp hq hle
        have hbudget : M6.Euclid.rank (M6.Euclid.cancel p q) ≤ fuel := by omega
        obtain ⟨hvalue, hcost⟩ := ih (M6.Euclid.cancel p q) q hbudget
        have hv : (M6.Euclid.remainderAux fuel (M6.Euclid.cancel p q) q).value = p % q :=
          hvalue.trans (M6.Euclid.cancel_mod p q)
        have hc : (M6.Euclid.remainderAux fuel (M6.Euclid.cancel p q) q).cancellations + 1 + M6.Euclid.rank (M6.Euclid.remainderAux fuel (M6.Euclid.cancel p q) q).value ≤ M6.Euclid.rank p := by
          omega
        simpa [M6.Euclid.remainderAux, hp, hq, hd, hle, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using And.intro hv hc

theorem M6.Euclid.remainder_correct : ∀ p q : M6.Euclid.BP, (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p ∧ (q ≠ 0 → M6.Euclid.rank (M6.Euclid.remainder p q).value < M6.Euclid.rank q) := by
  change ∀ p q : M6.Euclid.BP, (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p ∧ (q ≠ 0 → M6.Euclid.rank (M6.Euclid.remainder p q).value < M6.Euclid.rank q)
  intro p q
  have h : (M6.Euclid.remainder p q).value = p % q ∧ (M6.Euclid.remainder p q).cancellations + M6.Euclid.rank (M6.Euclid.remainder p q).value ≤ M6.Euclid.rank p := by
    simpa [M6.Euclid.remainder] using
      (M6.Euclid.remainder_aux_correct (M6.Euclid.rank p) p q (le_refl _))
  refine ⟨h.1, h.2, ?_⟩
  intro hq
  rw [h.1]
  apply ((M6.Euclid.rank_order (p % q) q).1).mpr
  exact Polynomial.degree_mod_lt p hq
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank q < fuel → (M6.Euclid.euclidAux fuel p q).value = EuclideanDomain.gcd q p ∧ (M6.Euclid.euclidAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclidAux fuel p q).rounds ≤ M6.Euclid.rank q
