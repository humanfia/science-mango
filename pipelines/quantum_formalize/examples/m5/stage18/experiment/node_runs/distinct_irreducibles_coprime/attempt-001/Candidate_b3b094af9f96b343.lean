import FrozenTarget_b3b094af9f96b343
theorem M5.FactorProduct.distinct_irreducibles_coprime : QuantumHarnessFrozenTarget := by
  change ∀ p q : M5.BinaryPolynomial, p.Monic → q.Monic → Irreducible p → Irreducible q → p ≠ q → IsCoprime p q
  intro p q hpm hqm hp hq hpq
  apply hp.coprime_iff_not_dvd.mpr
  rintro ⟨r, hr⟩
  rcases hq.isUnit_or_isUnit hr with hpu | hru
  · exact hp.not_isUnit hpu
  · rcases hru with ⟨u, hu⟩
    apply hpq
    apply Polynomial.eq_of_monic_of_associated hpm hqm
    exact ⟨u, by simpa only [hu] using hr.symm⟩
