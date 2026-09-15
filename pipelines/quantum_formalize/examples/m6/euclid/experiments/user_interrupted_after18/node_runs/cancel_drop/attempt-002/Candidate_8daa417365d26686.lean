import FrozenTarget_8daa417365d26686
theorem M6.Euclid.cancel_drop : QuantumHarnessFrozenTarget := by
  change ∀ p q : M6.Euclid.BP, p ≠ 0 → q ≠ 0 → q.degree ≤ p.degree → M6.Euclid.rank (M6.Euclid.cancel p q) < M6.Euclid.rank p
  intro p q hp hq hdeg
  apply ((M6.Euclid.rank_order (M6.Euclid.cancel p q) p).1).mpr
  have hmp := (M6.Euclid.binary_normalization p).1 hp
  have hmq := (M6.Euclid.binary_normalization q).1 hq
  simpa [M6.Euclid.cancel, hmp.leadingCoeff, mul_comm, mul_left_comm, mul_assoc] using
    (Polynomial.div_wf_lemma (p := p) (q := q) ⟨hdeg, hp⟩ hmq)
