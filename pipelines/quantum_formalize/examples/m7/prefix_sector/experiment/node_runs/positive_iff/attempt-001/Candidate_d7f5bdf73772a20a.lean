import FrozenTarget_d7f5bdf73772a20a
theorem M7.PrefixSector.positive_iff : QuantumHarnessFrozenTarget := by
  intro N w E A B WA WB hN hE hPrefix
  rw [M7.PrefixSector.exact_sector_count N w E A B WA WB hN hE hPrefix]
  exact_mod_cast (Finset.card_pos : 0 < (M7.PrefixSector.completions N w E A B WA WB).card ↔ (M7.PrefixSector.completions N w E A B WA WB).Nonempty)
