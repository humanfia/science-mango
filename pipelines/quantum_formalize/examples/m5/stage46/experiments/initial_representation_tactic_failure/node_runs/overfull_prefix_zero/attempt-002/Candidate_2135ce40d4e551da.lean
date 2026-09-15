import FrozenTarget_2135ce40d4e551da
theorem M5.PhysicalRecovery.overfull_prefix_zero : QuantumHarnessFrozenTarget := by
  classical
  intro N w F p hN hp hover
  have hbad : ∀ q ∈ M5.PhysicalRecovery.validWords N w F, ¬ p.IsPrefix q := by
    intro q hq hpq
    have hv : M5.PhysicalRecovery.wordValid N w F q := by
      unfold M5.PhysicalRecovery.validWords at hq
      aesop
    have hlen : q.length = M5.PhysicalRecovery.decisionCount N := by
      unfold M5.PhysicalRecovery.wordValid at hv
      tauto
    have hcards : (M5.PhysicalRecovery.selectedA N q).card = w ∧
        (M5.PhysicalRecovery.selectedB N q).card = w := by
      unfold M5.PhysicalRecovery.wordValid M5.PhysicalRecovery.ValidSupports at hv
      tauto
    have he := (M5.PhysicalRecovery.prefix_extension N p q hN hp hlen).mp hpq
    have ha := Finset.card_le_card he.1
    have hb := Finset.card_le_card he.2.2.1
    omega
  have htake : ∀ q ∈ M5.PhysicalRecovery.validWords N w F,
      q.take p.length ≠ p := by
    intro q hq ht
    apply hbad q hq
    refine ⟨q.drop p.length, ?_⟩
    rw [← ht]
    exact List.take_append_drop p.length q
  unfold M5.PrefixPartition.count
  simp_all [Finset.filter_eq_empty_iff]
