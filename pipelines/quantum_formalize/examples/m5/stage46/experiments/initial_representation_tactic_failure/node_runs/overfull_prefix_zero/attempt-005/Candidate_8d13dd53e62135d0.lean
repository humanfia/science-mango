import FrozenTarget_8d13dd53e62135d0
theorem M5.PhysicalRecovery.overfull_prefix_zero : QuantumHarnessFrozenTarget := by
  classical
  intro N w F p hN hp hover
  unfold M5.PrefixPartition.count
  apply Int.ofNat_eq_zero.mpr
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro q hq hpq
  have hv := (Finset.mem_filter.mp hq).2
  change M5.PhysicalRecovery.wordValid N w F q at hv
  unfold M5.PhysicalRecovery.wordValid M5.PhysicalRecovery.ValidSupports at hv
  have hlen : q.length = M5.PhysicalRecovery.decisionCount N := by tauto
  have ha : (M5.PhysicalRecovery.selectedA N q).card = w := by tauto
  have hb : (M5.PhysicalRecovery.selectedB N q).card = w := by tauto
  have hs := (M5.PhysicalRecovery.prefix_extension N p q hN hp hlen).mp hpq
  have hca := Finset.card_le_card hs.1
  have hcb := Finset.card_le_card hs.2.2.1
  rcases hover with hover | hover
  · omega
  · omega
