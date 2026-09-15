import FrozenTarget_f081fd572457db1f
theorem M6.Transfer.mass_add : QuantumHarnessFrozenTarget := by
  classical
  change ∀ p q : Polynomial ℤ, M6.Transfer.polynomialMass (p + q) ≤ M6.Transfer.polynomialMass p + M6.Transfer.polynomialMass q
  intro p q
  unfold M6.Transfer.polynomialMass
  rw [Polynomial.sum_eq_of_subset (p := p + q) (fun _ c : ℤ => c.natAbs) (fun _ => rfl) (Polynomial.support_add p q),
      Polynomial.sum_eq_of_subset (p := p) (fun _ c : ℤ => c.natAbs) (fun _ => rfl) (Finset.subset_union_left : p.support ⊆ p.support ∪ q.support),
      Polynomial.sum_eq_of_subset (p := q) (fun _ c : ℤ => c.natAbs) (fun _ => rfl) (Finset.subset_union_right : q.support ⊆ p.support ∪ q.support),
      ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [Polynomial.coeff_add] using Int.natAbs_add_le (p.coeff i) (q.coeff i)
