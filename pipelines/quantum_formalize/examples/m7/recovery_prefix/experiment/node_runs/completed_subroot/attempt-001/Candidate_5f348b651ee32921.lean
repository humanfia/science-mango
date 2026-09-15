import FrozenTarget_5f348b651ee32921
theorem M7.RecoveryPrefix.completed_subroot : QuantumHarnessFrozenTarget := by
  intro N inst w E p
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hp := M7.PrefixBits.base N hN p
  have hr := M7.PrefixBits.base N hN []
  intro x hx
  change x ∈ M7.ResiduePrefix.completed N w E (M7.PrefixBits.A N p) (M7.PrefixBits.B N p) (M7.PrefixBits.WA N p) (M7.PrefixBits.WB N p) at hx
  change x ∈ M7.ResiduePrefix.completed N w E (M7.PrefixBits.A N []) (M7.PrefixBits.B N []) (M7.PrefixBits.WA N []) (M7.PrefixBits.WB N [])
  obtain ⟨hw, hv⟩ := (M7.ResiduePrefix.completed_membership N w E _ _ _ _ hp x).mp hx
  apply (M7.ResiduePrefix.completed_membership N w E _ _ _ _ hr x).mpr
  refine ⟨?_, hv⟩
  obtain ⟨hA, hB, hWA, hWB⟩ := M7.PrefixBits.root N hN
  rw [hA, hB, hWA, hWB]
  simp only [M7.PrefixCompleted.Base, M7.PrefixCompleted.Within, Finset.subset_iff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hp hw ⊢
  grind
