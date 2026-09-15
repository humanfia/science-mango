import FrozenTarget_dbbf38e02450a807
theorem M6.ActualCounts.zero_signature_no_logicals : QuantumHarnessFrozenTarget := by
  intro N inst a b ha hb hf
  apply Finset.card_eq_zero.mp
  have h := M6.ActualCounts.logical_card N a b ha hb
  simp only [hf, Nat.add_zero, Nat.sub_zero, sub_self] at h
  exact_mod_cast h
