import FrozenTarget_b405bf1bcbb87d70
theorem M6.ActualCounts.f_le_order : QuantumHarnessFrozenTarget := by
  intro N inst a b
  change (M6.Cyclic.signature a b (M6.Cyclic.modulus N)).natDegree ≤ N
  have hm := M6.Coordinates.modulus_monic_degree N
  have hd := (M6.Cyclic.signature_divides a b (M6.Cyclic.modulus N)).2.2
  simpa only [hm.2] using Polynomial.natDegree_le_of_dvd hd hm.1.ne_zero
