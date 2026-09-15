import M6TransferCoefficients

theorem M6.Transfer.mass_add : ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p+q) ≤ M6.Transfer.polynomialMass p + M6.Transfer.polynomialMass q := by
  change ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p + q) ≤ M6.Transfer.polynomialMass p + M6.Transfer.polynomialMass q
  intro p q
  classical
  unfold M6.Transfer.polynomialMass
  have hp : p.support ⊆ p.support ∪ q.support := Finset.subset_union_left
  have hq : q.support ⊆ p.support ∪ q.support := Finset.subset_union_right
  have hpq : (p + q).support ⊆ p.support ∪ q.support := Polynomial.support_add
  rw [Polynomial.sum_eq_of_subset (p := p + q) (fun (_ : ℕ) (c : ℤ) => c.natAbs) (by intro i; rfl) hpq,
      Polynomial.sum_eq_of_subset (p := p) (fun (_ : ℕ) (c : ℤ) => c.natAbs) (by intro i; rfl) hp,
      Polynomial.sum_eq_of_subset (p := q) (fun (_ : ℕ) (c : ℤ) => c.natAbs) (by intro i; rfl) hq,
      ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [Polynomial.coeff_add] using Int.natAbs_add_le (p.coeff i) (q.coeff i)

theorem M6.Transfer.mass_basic : M6.Transfer.polynomialMass (0 : Polynomial ℤ) = 0 ∧ M6.Transfer.polynomialMass (1 : Polynomial ℤ) = 1 ∧ (∀ (n : ℕ) (c : ℤ), M6.Transfer.polynomialMass (Polynomial.monomial n c) = c.natAbs) ∧ ∀ (p : Polynomial ℤ) (d : ℕ), (p.coeff d).natAbs ≤ M6.Transfer.polynomialMass p := by
  let QuantumHarnessFrozenTarget : Prop := (
    M6.Transfer.polynomialMass (0 : Polynomial ℤ) = 0 ∧ M6.Transfer.polynomialMass (1 : Polynomial ℤ) = 1 ∧ (∀ (n : ℕ) (c : ℤ), M6.Transfer.polynomialMass (Polynomial.monomial n c) = c.natAbs) ∧ ∀ (p : Polynomial ℤ) (d : ℕ), (p.coeff d).natAbs ≤ M6.Transfer.polynomialMass p
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  have hm : ∀ (n : ℕ) (c : ℤ), M6.Transfer.polynomialMass (Polynomial.monomial n c) = c.natAbs := by
    intro n c
    simp [M6.Transfer.polynomialMass, Polynomial.sum_monomial_index]
  refine ⟨?_, ?_, hm, ?_⟩
  · simp [M6.Transfer.polynomialMass]
  · simpa using hm 0 1
  · intro p d
    by_cases h : p.coeff d = 0
    · simp [h]
    · change (p.coeff d).natAbs ≤ ∑ n ∈ p.support, (p.coeff n).natAbs
      exact Finset.single_le_sum
        (f := fun n => (p.coeff n).natAbs)
        (fun n _ => Nat.zero_le ((p.coeff n).natAbs))
        (Polynomial.mem_support_iff.mpr h)

theorem M6.Transfer.mass_sum : ∀ (I : Type) (s : Finset I) (f : I → Polynomial ℤ), M6.Transfer.polynomialMass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, M6.Transfer.polynomialMass (f i) := by
  change ∀ (I : Type) (s : Finset I) (f : I → Polynomial ℤ), M6.Transfer.polynomialMass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, M6.Transfer.polynomialMass (f i)
  intro I s f
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, M6.Transfer.mass_basic.1, le_refl]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (M6.Transfer.mass_add (f a) (∑ i ∈ s, f i)).trans
        (Nat.add_le_add_left ih (M6.Transfer.polynomialMass (f a)))

theorem M6.Transfer.mass_mul : ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p*q) ≤ M6.Transfer.polynomialMass p * M6.Transfer.polynomialMass q := by
  change ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p * q) ≤ M6.Transfer.polynomialMass p * M6.Transfer.polynomialMass q
  intro p q
  classical
  rw [Polynomial.mul_eq_sum_sum]
  refine (M6.Transfer.mass_sum ℕ p.support _).trans ?_
  calc
    _ ≤ ∑ i ∈ p.support, (p.coeff i).natAbs * M6.Transfer.polynomialMass q := by
      apply Finset.sum_le_sum
      intro i hi
      change M6.Transfer.polynomialMass (∑ j ∈ q.support, Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) ≤ (p.coeff i).natAbs * M6.Transfer.polynomialMass q
      refine (M6.Transfer.mass_sum ℕ q.support _).trans ?_
      simp only [M6.Transfer.mass_basic.2.2.1, Int.natAbs_mul]
      change (∑ j ∈ q.support, (p.coeff i).natAbs * (q.coeff j).natAbs) ≤ (p.coeff i).natAbs * (∑ j ∈ q.support, (q.coeff j).natAbs)
      rw [Finset.mul_sum]
    _ = M6.Transfer.polynomialMass p * M6.Transfer.polynomialMass q := by
      change (∑ i ∈ p.support, (p.coeff i).natAbs * M6.Transfer.polynomialMass q) = (∑ i ∈ p.support, (p.coeff i).natAbs) * M6.Transfer.polynomialMass q
      rw [Finset.sum_mul]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (v : M6.Transfer.Memory R → Polynomial ℤ), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.propagate W v) ≤ 8 * M6.Transfer.rowMass v
