import FrozenTarget_131d21ebf99fb0e1
theorem M5.PhysicalRecovery.state_domains : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (p : List Bool), 0 < N → p.length ≤ M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.StateOK N p
  intro N p hN hp
  unfold M5.PhysicalRecovery.StateOK
  simp only [M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selectedB,
    M5.PhysicalRecovery.availableA, M5.PhysicalRecovery.availableB,
    M5.PhysicalRecovery.selected, M5.PhysicalRecovery.available,
    Finset.subset_iff, Finset.disjoint_left, Finset.mem_insert,
    Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  repeat' first
    | omega
    | assumption
    | apply And.intro
    | intro
    | match goal with
      | h : ∃ _, _ ⊢ _ => rcases h with ⟨i, hi⟩
      | h : _ ∧ _ ⊢ _ => rcases h with ⟨h₁, h₂⟩
      | h : _ ∨ _ ⊢ _ => rcases h with h₁ | h₂
    | simp_all
