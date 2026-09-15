import FrozenTarget_a8b12e4332e3c940
theorem M7.RawCoverage.root_membership : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E c
  change c ∈ M7.ResiduePrefix.completed N w E (M7.PrefixBits.A N []) (M7.PrefixBits.B N []) (M7.PrefixBits.WA N []) (M7.PrefixBits.WB N []) ↔ _
  rw [M7.PrefixOrbit.membership N w E _ _ _ _ (M7.PrefixBits.base N (NeZero.pos N) []) c]
  have hr := M7.PrefixBits.root N (NeZero.pos N)
  have hB : M7.PrefixBits.B N [] = M7.PrefixBits.A N [] := hr.2.1.trans hr.1.symm
  have hWB : M7.PrefixBits.WB N [] = M7.PrefixBits.WA N [] := hr.2.2.2.trans hr.2.2.1.symm
  rw [hB, hWB, M7.RawCoverage.root_within N c.1, M7.RawCoverage.root_within N c.2]
  simp only [M7.RawCoverage.Queried, and_assoc]
