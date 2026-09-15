import FrozenTarget_ce6fbe5c496f6498
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
  have htake : ∀ q ∈ M5.PhysicalRecovery.validWords N w F,
      q.take p.length ≠ p := by
    intro q hq he
    apply hnone q hq
    refine ⟨q.drop p.length, ?_⟩
    calc
      p ++ q.drop p.length = q.take p.length ++ q.drop p.length :=
        congrArg (fun r => r ++ q.drop p.length) he.symm
      _ = q := List.take_append_drop p.length q
  simp [M5.PrefixPartition.count, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, htake, hnone, eq_comm]
