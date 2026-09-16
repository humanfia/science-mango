import FrozenTarget_b824e5ff67ebe481
theorem M8.Anchor.translation_reconstruction : QuantumHarnessFrozenTarget := by
  intro N inst c g h
  classical
  rcases g with ⟨u, e, s, t⟩
  cases e <;> simp [M8.Anchor.Anchored, M7.Action.act, M7.Action.affine, Finset.mem_image] at h
  all_goals
    rcases h with ⟨⟨a, ha, hsa⟩, ⟨b, hb, htb⟩⟩
    have hs : -((u : ZMod N) * a) = s := by
      linear_combination -hsa
    have ht : -((u : ZMod N) * b) = t := by
      linear_combination -htb
    refine ⟨a, b, ?_, ?_⟩
    · exact ⟨ha, hb⟩
    · simp [M8.Anchor.record, hs, ht]
