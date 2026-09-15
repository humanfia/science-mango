import FrozenTarget_c29aa3a71a33dcd5
theorem M5.PhysicalRecovery.overfull_prefix_zero : QuantumHarnessFrozenTarget := by
  classical
  intro N w F p hN hp hover
  have hnone : ∀ q ∈ M5.PhysicalRecovery.validWords N w F, ¬ p.IsPrefix q := by
    intro q hq hpq
    have hv : M5.PhysicalRecovery.wordValid N w F q := by
      unfold M5.PhysicalRecovery.validWords at hq
      exact (Finset.mem_filter.mp hq).2
    have hlen : q.length = M5.PhysicalRecovery.decisionCount N := by
      unfold M5.PhysicalRecovery.wordValid at hv
      exact hv.1
    have hcards : (M5.PhysicalRecovery.selectedA N q).card = w ∧
        (M5.PhysicalRecovery.selectedB N q).card = w := by
      unfold M5.PhysicalRecovery.wordValid M5.PhysicalRecovery.ValidSupports at hv
      tauto
    have hext := (M5.PhysicalRecovery.prefix_extension N p q hN hp hlen).mp hpq
    have ha := Finset.card_le_card hext.1
    have hb := Finset.card_le_card hext.2.2.1
    omega
  have hempty : ((M5.PhysicalRecovery.validWords N w F).filter
      (fun q => p.IsPrefix q)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    exact hnone
  unfold M5.PrefixPartition.count
  rw [hempty]
  simp
