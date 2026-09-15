import FrozenTarget_d0e6c719ac491b9e
theorem M6.Euclid.euclid_aux_correct : QuantumHarnessFrozenTarget := by
  change ∀ (fuel : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank q < fuel → (M6.Euclid.euclidAux fuel p q).value = EuclideanDomain.gcd q p ∧ (M6.Euclid.euclidAux fuel p q).cancellations + M6.Euclid.rank (M6.Euclid.euclidAux fuel p q).value ≤ M6.Euclid.rank p + M6.Euclid.rank q ∧ (M6.Euclid.euclidAux fuel p q).rounds ≤ M6.Euclid.rank q
  intro fuel
  induction fuel with
  | zero =>
      intro p q hf
      omega
  | succ fuel ih =>
      intro p q hf
      by_cases hq : q = 0
      · subst q
        simp [M6.Euclid.euclidAux, M6.Euclid.rank, EuclideanDomain.gcd_zero_left, (M6.Euclid.binary_normalization p).2]
      · obtain ⟨hrvalue, hrcost, hrdrop⟩ := M6.Euclid.remainder_correct p q
        have hdrop := hrdrop hq
        have hbudget : M6.Euclid.rank (M6.Euclid.remainder p q).value < fuel := by omega
        obtain ⟨hvalue, hcost, hrounds⟩ := ih q (M6.Euclid.remainder p q).value hbudget
        have hv : (M6.Euclid.euclidAux fuel q (M6.Euclid.remainder p q).value).value = EuclideanDomain.gcd q p := by
          calc
            _ = EuclideanDomain.gcd (M6.Euclid.remainder p q).value q := hvalue
            _ = EuclideanDomain.gcd (p % q) q := by rw [hrvalue]
            _ = EuclideanDomain.gcd q p := (EuclideanDomain.gcd_val q p).symm
        simp only [M6.Euclid.euclidAux, hq, ↓reduceIte]
        refine ⟨hv, ?_, ?_⟩ <;> omega
