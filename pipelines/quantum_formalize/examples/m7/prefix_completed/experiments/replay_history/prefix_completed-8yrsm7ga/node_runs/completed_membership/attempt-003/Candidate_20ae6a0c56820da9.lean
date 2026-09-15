import FrozenTarget_20ae6a0c56820da9
theorem M7.PrefixCompleted.completed_membership : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB hA hB x
  change x ∈ (M7.PrefixSector.completions N w E A B WA WB).image (fun y => (A ∪ y.1, B ∪ y.2)) ↔ _
  constructor
  · intro hx
    obtain ⟨⟨U, V⟩, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨F, hF, hy⟩ := (M7.PrefixSector.completion_membership N w E A B WA WB (U, V)).mp hy
    simp [M5.ConditionalCount.validCompletions] at hy
    have hU : U ⊆ WA := by aesop
    have hV : V ⊆ WB := by aesop
    have hdU : Disjoint A U := hA.mono_right hU
    have hdV : Disjoint B V := hB.mono_right hV
    have hcU := Finset.card_union_of_disjoint hdU
    have hcV := Finset.card_union_of_disjoint hdV
    have hwA : (A ∪ U).card = w := by omega
    have hwB : (B ∪ V).card = w := by omega
    change (A ⊆ A ∪ U ∧ A ∪ U ⊆ A ∪ WA ∧ B ⊆ B ∪ V ∧ B ∪ V ⊆ B ∪ WB) ∧ _
    refine ⟨⟨Finset.subset_union_left, Finset.union_subset_union (by rfl) hU, Finset.subset_union_left, Finset.union_subset_union (by rfl) hV⟩, ?_⟩
    unfold M7.PrefixCompleted.Valid
    dsimp
    refine ⟨hwA, hwB, ?_, ?_⟩ <;> aesop
  · rintro ⟨hx, hv⟩
    rcases hx with ⟨hAX, hXA, hBX, hXB⟩
    rcases hv with ⟨hcA, hcB, hg, hs⟩
    have hUA : A ∪ (x.1 \ A) = x.1 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hi | ⟨hi, _⟩)
        · exact hAX hi
        · exact hi
      · intro hi
        by_cases ha : i ∈ A <;> aesop
    have hUB : B ∪ (x.2 \ B) = x.2 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hi | ⟨hi, _⟩)
        · exact hBX hi
        · exact hi
      · intro hi
        by_cases hb : i ∈ B <;> aesop
    have hRA : x.1 \ A ⊆ WA := by
      intro i hi
      obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hXA hi)).resolve_left hn
    have hRB : x.2 \ B ⊆ WB := by
      intro i hi
      obtain ⟨hi, hn⟩ := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hXB hi)).resolve_left hn
    have hCA : (x.1 \ A).card = w - A.card := by rw [Finset.card_sdiff hAX, hcA]
    have hCB : (x.2 \ B).card = w - B.card := by rw [Finset.card_sdiff hBX, hcB]
    have hleA : A.card ≤ w := hcA ▸ Finset.card_le_card hAX
    have hleB : B.card ≤ w := hcB ▸ Finset.card_le_card hBX
    apply Finset.mem_image.mpr
    refine ⟨(x.1 \ A, x.2 \ B), ?_, ?_⟩
    · apply (M7.PrefixSector.completion_membership N w E A B WA WB _).mpr
      refine ⟨_, hs, ?_⟩
      simp [M5.ConditionalCount.validCompletions, hRA, hRB, hCA, hCB, hUA, hUB, hcA, hcB, hg, hleA, hleB]
    · simpa only [hUA, hUB] using x.eta
