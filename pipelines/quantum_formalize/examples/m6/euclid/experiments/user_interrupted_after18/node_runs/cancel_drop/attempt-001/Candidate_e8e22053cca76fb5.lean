import FrozenTarget_e8e22053cca76fb5
theorem M6.Euclid.cancel_drop : QuantumHarnessFrozenTarget := by
  change ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p
  intro p q hp hq hdeg
  apply ((M6.Euclid.rank_order (M6.Euclid.cancel p q) p).1).2
  have hmp := (M6.Euclid.binary_normalization p).1 hp
  have hmq := (M6.Euclid.binary_normalization q).1 hq
  have hd : (p - q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree))).degree < p.degree := by
    apply Polynomial.div_wf_lemma <;> assumption
  simpa [M6.Euclid.cancel, hmp.leadingCoeff, hmq.leadingCoeff, mul_assoc, mul_comm, mul_left_comm] using hd
