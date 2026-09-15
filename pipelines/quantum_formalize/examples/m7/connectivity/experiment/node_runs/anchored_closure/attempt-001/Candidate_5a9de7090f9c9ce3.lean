import FrozenTarget_5a9de7090f9c9ce3
theorem M7.Connectivity.anchored_closure : QuantumHarnessFrozenTarget := by
  intro N inst A B hA hB
  apply le_antisymm
  · apply (AddSubgroup.closure_le _).2
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨a, ha, b, hb, h⟩
      subst x
      exact (AddSubgroup.closure ((A : Set (ZMod N)) ∪ (B : Set (ZMod N)))).sub_mem
        (AddSubgroup.subset_closure (Or.inl ha))
        (AddSubgroup.subset_closure (Or.inl hb))
    · rcases hx with ⟨a, ha, b, hb, h⟩
      subst x
      exact (AddSubgroup.closure ((A : Set (ZMod N)) ∪ (B : Set (ZMod N)))).sub_mem
        (AddSubgroup.subset_closure (Or.inr ha))
        (AddSubgroup.subset_closure (Or.inr hb))
  · apply (AddSubgroup.closure_le _).2
    intro x hx
    apply AddSubgroup.subset_closure
    rcases hx with hx | hx
    · left
      refine ⟨x, hx, 0, hA, ?_⟩
      simp
    · right
      refine ⟨x, hx, 0, hB, ?_⟩
      simp
