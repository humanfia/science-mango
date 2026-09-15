import FrozenTarget_cc6e7524704e6680
theorem M5.Signature.ordinary_gcd_period_bound : QuantumHarnessFrozenTarget := by
  change ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → 0 < M5.signaturePeriod (EuclideanDomain.gcd a b) ∧ M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ b.natDegree
  intro a b ha hb
  obtain ⟨hm, hc, hd⟩ := M5.Signature.ordinary_gcd_properties a b ha hb
  have hl := M5.Period.period_law (EuclideanDomain.gcd a b) hm hc
  have hbound := M5.Period.period_cardinality_bound (EuclideanDomain.gcd a b) hm hc
  constructor
  · aesop
  · calc
      M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ (EuclideanDomain.gcd a b).natDegree := by aesop
      _ ≤ 2 ^ b.natDegree := by gcongr
