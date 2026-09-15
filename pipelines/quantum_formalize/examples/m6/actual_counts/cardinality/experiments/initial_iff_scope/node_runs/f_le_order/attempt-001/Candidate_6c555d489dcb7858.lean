import FrozenTarget_6c555d489dcb7858
theorem M6.ActualCounts.f_le_order : QuantumHarnessFrozenTarget := by
  intro N inst a b
  change (M6.Cyclic.signature a b (M6.Cyclic.modulus N)).natDegree ≤ N
  have hm := M6.Coordinates.modulus_monic_degree N
  calc
    (M6.Cyclic.signature a b (M6.Cyclic.modulus N)).natDegree ≤
        (M6.Cyclic.modulus N).natDegree :=
      Polynomial.natDegree_le_of_dvd hm.1.ne_zero
        (M6.Cyclic.signature_divides a b (M6.Cyclic.modulus N)).2.2
    _ = N := hm.2
