import FrozenTarget_686413abd323ea69
theorem M5.PhysicalRecovery.overfull_prefix_zero : QuantumHarnessFrozenTarget := by
  intro N w F p hN hp hover
  classical
  have hnone : ∀ q ∈ M5.PhysicalRecovery.validWords N w F, ¬ p.IsPrefix q := by
    intro q hq hpq
    have hv : M5.PhysicalRecovery.wordValid N w F q :=
      (Finset.mem_filter.mp hq).2
    unfold M5.PhysicalRecovery.wordValid M5.PhysicalRecovery.ValidSupports at hv
    have hlen : q.length = M5.PhysicalRecovery.decisionCount N := by tauto
    have hA : (M5.PhysicalRecovery.selectedA N q).card = w := by tauto
    have hB : (M5.PhysicalRecovery.selectedB N q).card = w := by tauto
    have hs := (M5.PhysicalRecovery.prefix_extension N p q hN hp hlen).mp hpq
    have hcA := Finset.card_le_card hs.1
    have hcB := Finset.card_le_card hs.2.2.1
    omega
  unfold M5.PrefixPartition.count
  simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact hnone
