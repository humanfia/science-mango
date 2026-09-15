import FrozenTarget_28980492f4bbdafa
theorem M5.PhysicalRecovery.overfull_prefix_zero : QuantumHarnessFrozenTarget := by
  classical
  intro N w F p hN hp hover
  change (((M5.PhysicalRecovery.validWords N w F).filter (fun q => p.IsPrefix q)).card : ℤ) = 0
  have hempty : (M5.PhysicalRecovery.validWords N w F).filter (fun q => p.IsPrefix q) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro q hq
    obtain ⟨hq, hpq⟩ := Finset.mem_filter.mp hq
    have hv : M5.PhysicalRecovery.wordValid N w F q := by
      simpa only [M5.PhysicalRecovery.validWords, Finset.mem_filter] using hq |>.2
    unfold M5.PhysicalRecovery.wordValid M5.PhysicalRecovery.ValidSupports at hv
    have hlen : q.length = M5.PhysicalRecovery.decisionCount N := by tauto
    have hA : (M5.PhysicalRecovery.selectedA N q).card = w := by tauto
    have hB : (M5.PhysicalRecovery.selectedB N q).card = w := by tauto
    have he := (M5.PhysicalRecovery.prefix_extension N p q hN hp hlen).mp hpq
    have hcA := Finset.card_le_card he.1
    have hcB := Finset.card_le_card he.2.2.1
    omega
  rw [hempty]
  simp
