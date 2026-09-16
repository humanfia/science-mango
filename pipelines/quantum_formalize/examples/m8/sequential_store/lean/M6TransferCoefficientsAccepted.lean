import M6TransferCoefficients

theorem M6.Transfer.layers_degree : ∀ (R : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start finish : M6.Transfer.Memory R) (n : ℕ), (∀ i m t, (W i m t).natDegree ≤ 2) → (M6.Transfer.layers W start n finish).natDegree ≤ 2*n := by
  classical
  intro R W start finish n hW
  induction n generalizing finish with
  | zero =>
      by_cases h : finish = start <;>
        simp [M6.Transfer.layers, h]
  | succ n ih =>
      simp only [M6.Transfer.layers, M6.Transfer.propagate]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro m hm
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro t ht
      split_ifs with h
      · have hmul := Polynomial.natDegree_mul_le (p := M6.Transfer.layers W start n m) (q := W n m t)
        exact (hmul.trans (Nat.add_le_add (ih m) (hW n m t))).trans_eq (by simp [Nat.mul_succ])
      · simp

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

theorem M6.Transfer.propagate_mass : ∀ (R : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (v : M6.Transfer.Memory R → Polynomial ℤ), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.propagate W v) ≤ 8 * M6.Transfer.rowMass v := by
  change ∀ (R : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (v : M6.Transfer.Memory R → Polynomial ℤ), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.propagate W v) ≤ 8 * M6.Transfer.rowMass v
  intro R W v hW
  classical
  have hc : Fintype.card M6.Transfer.Bit = 2 := by
    simp [M6.Transfer.Bit]
  calc
    M6.Transfer.rowMass (M6.Transfer.propagate W v)
        ≤ ∑ n : M6.Transfer.Memory R, ∑ m : M6.Transfer.Memory R,
            ∑ t : M6.Transfer.Bit, M6.Transfer.polynomialMass
              (if M6.Transfer.shift m t = n then v m * W m t else 0) := by
      unfold M6.Transfer.rowMass M6.Transfer.propagate
      apply Finset.sum_le_sum
      intro n hn
      refine (M6.Transfer.mass_sum _ Finset.univ _).trans ?_
      apply Finset.sum_le_sum
      intro m hm
      exact M6.Transfer.mass_sum _ Finset.univ _
    _ = ∑ m : M6.Transfer.Memory R, ∑ t : M6.Transfer.Bit,
          M6.Transfer.polynomialMass (v m * W m t) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [apply_ite, M6.Transfer.mass_basic.1]
      simp
    _ ≤ ∑ m : M6.Transfer.Memory R, ∑ t : M6.Transfer.Bit,
          M6.Transfer.polynomialMass (v m) * 4 := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro t ht
      exact (M6.Transfer.mass_mul (v m) (W m t)).trans
        (Nat.mul_le_mul_left _ (hW m t))
    _ = ∑ m : M6.Transfer.Memory R, 8 * M6.Transfer.polynomialMass (v m) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
      ring
    _ = 8 * M6.Transfer.rowMass v := by
      unfold M6.Transfer.rowMass
      rw [Finset.mul_sum]

theorem M6.Transfer.layers_mass : ∀ (R : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start : M6.Transfer.Memory R) (n : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.layers W start n) ≤ 8^n := by
  change ∀ (R : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start : M6.Transfer.Memory R) (n : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → M6.Transfer.rowMass (M6.Transfer.layers W start n) ≤ 8 ^ n
  intro R W start n hW
  classical
  induction n with
  | zero =>
      simp [M6.Transfer.layers, M6.Transfer.rowMass, apply_ite,
        M6.Transfer.mass_basic.1, M6.Transfer.mass_basic.2.1]
  | succ n ih =>
      change M6.Transfer.rowMass (M6.Transfer.propagate (W n) (M6.Transfer.layers W start n)) ≤ 8 ^ (n + 1)
      calc
        _ ≤ 8 * M6.Transfer.rowMass (M6.Transfer.layers W start n) :=
          M6.Transfer.propagate_mass R (W n) (M6.Transfer.layers W start n) (hW n)
        _ ≤ 8 * 8 ^ n := Nat.mul_le_mul_left 8 ih
        _ = 8 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

theorem M6.Transfer.trace_coefficient_bound : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → ((M6.Transfer.arrayTrace W N).coeff d).natAbs ≤ 2^R * 8^N := by
  change ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → ((M6.Transfer.arrayTrace W N).coeff d).natAbs ≤ 2 ^ R * 8 ^ N
  intro R N W d hW
  classical
  have hc : Fintype.card (M6.Transfer.Memory R) = 2 ^ R := by
    simp [M6.Transfer.Memory, M6.Transfer.Bit]
  calc
    ((M6.Transfer.arrayTrace W N).coeff d).natAbs
        ≤ M6.Transfer.polynomialMass (M6.Transfer.arrayTrace W N) :=
      M6.Transfer.mass_basic.2.2.2 _ d
    _ ≤ ∑ start : M6.Transfer.Memory R,
          M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) := by
      unfold M6.Transfer.arrayTrace
      exact M6.Transfer.mass_sum _ Finset.univ _
    _ ≤ ∑ _start : M6.Transfer.Memory R, (8 ^ N : ℕ) := by
      apply Finset.sum_le_sum
      intro start hstart
      have hd : M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) ≤
          M6.Transfer.rowMass (M6.Transfer.layers W start N) := by
        unfold M6.Transfer.rowMass
        exact Finset.single_le_sum
          (fun m _ => Nat.zero_le (M6.Transfer.polynomialMass (M6.Transfer.layers W start N m)))
          (Finset.mem_univ start)
      exact hd.trans (M6.Transfer.layers_mass R W start N hW)
    _ = 2 ^ R * 8 ^ N := by
      simp [hc, nsmul_eq_mul]
#print axioms M6.Transfer.layers_degree
#print axioms M6.Transfer.mass_add
#print axioms M6.Transfer.mass_basic
#print axioms M6.Transfer.mass_sum
#print axioms M6.Transfer.mass_mul
#print axioms M6.Transfer.propagate_mass
#print axioms M6.Transfer.layers_mass
#print axioms M6.Transfer.trace_coefficient_bound
