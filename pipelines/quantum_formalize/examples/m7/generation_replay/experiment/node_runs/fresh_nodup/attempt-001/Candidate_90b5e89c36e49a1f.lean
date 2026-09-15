import FrozenTarget_90b5e89c36e49a1f
theorem M7.GenerationReplay.fresh_nodup : QuantumHarnessFrozenTarget := by
  classical
  intro N inst w E bases es
  induction es generalizing bases with
  | nil =>
      intro h
      simp
  | cons e es ih =>
      intro h
      change e.representative ∉ bases ∧ _ ∧ _ ∧ M7.GenerationReplay.FreshFrom w E (insert e.representative bases) es at h
      rcases h with ⟨hfresh, _, _, htail⟩
      obtain ⟨hnd, hdisjoint⟩ := ih (insert e.representative bases) htail
      constructor
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, hnd⟩
        intro hm
        obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
        exact hdisjoint a ha (by simp [heq])
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hfresh
        · intro hb
          exact hdisjoint a ha (Finset.mem_insert_of_mem hb)
