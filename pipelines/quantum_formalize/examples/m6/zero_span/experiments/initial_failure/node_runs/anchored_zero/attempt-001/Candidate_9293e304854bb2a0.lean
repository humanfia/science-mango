import FrozenTarget_9293e304854bb2a0
theorem M6.ZeroSpan.anchored_zero : QuantumHarnessFrozenTarget := by
  change ∀ (a b : M6.Final.BP), a.coeff 0 = 1 → b.coeff 0 = 1 → M6.ActualTransfer.span a b = 0 → a = 1 ∧ b = 1
  intro a b ha hb hspan
  change max a.natDegree b.natDegree = 0 at hspan
  have hda : a.natDegree = 0 := by omega
  have hdb : b.natDegree = 0 := by omega
  constructor
  · simpa [ha] using (Polynomial.eq_C_of_natDegree_eq_zero hda)
  · simpa [hb] using (Polynomial.eq_C_of_natDegree_eq_zero hdb)
