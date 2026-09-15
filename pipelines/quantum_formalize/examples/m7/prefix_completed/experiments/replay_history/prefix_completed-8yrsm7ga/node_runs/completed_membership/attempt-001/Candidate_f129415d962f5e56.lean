import FrozenTarget_f129415d962f5e56
theorem M7.PrefixCompleted.completed_membership : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB hA hB x
  change x ∈ (M7.PrefixSector.completions N w E A B WA WB).image (fun y => (A ∪ y.1, B ∪ y.2)) ↔ _
  constructor
  · intro hx
    obtain ⟨⟨U, V⟩, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨F, hF, hy⟩ := (M7.PrefixSector.completion_membership N w E A B WA WB (U, V)).mp hy
    simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powersetCard, Prod.fst, Prod.snd] at hy
    split_ifs at hy
    all_goals try simp only [Finset.not_mem_empty, false_and, and_false] at hy
    all_goals
      have hU : U ⊆ WA := by aesop
      have hV : V ⊆ WB := by aesop
      have hcA := Finset.card_union_of_disjoint (hA.mono_right hU)
      have hcB := Finset.card_union_of_disjoint (hB.mono_right hV)
      have hwA : (A ∪ U).card = w := by omega
      have hwB : (B ∪ V).card = w := by omega
      constructor
      · change A ⊆ A ∪ U ∧ A ∪ U ⊆ A ∪ WA ∧ B ⊆ B ∪ V ∧ B ∪ V ⊆ B ∪ WB
        exact ⟨Finset.subset_union_left, Finset.union_subset_union (Subset.refl _) hU,
          Finset.subset_union_left, Finset.union_subset_union (Subset.refl _) hV⟩
      · unfold M7.PrefixCompleted.Valid
        dsimp only
        exact ⟨hwA, hwB, by aesop⟩
  · rintro ⟨hwithin, hvalid⟩
    rcases hwithin with ⟨hAX, hXA, hBX, hXB⟩
    rcases hvalid with ⟨hwA, hwB, hg, hs⟩
    have hU : x.1 \ A ⊆ WA := by
      intro i hi
      have hi' := Finset.mem_sdiff.mp hi
      have := Finset.mem_union.mp (hXA hi'.1)
      aesop
    have hV : x.2 \ B ⊆ WB := by
      intro i hi
      have hi' := Finset.mem_sdiff.mp hi
      have := Finset.mem_union.mp (hXB hi'.1)
      aesop
    have hu : A ∪ (x.1 \ A) = x.1 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hi | hi)
        · exact hAX hi
        · exact hi.1
      · intro hi
        by_cases ha : i ∈ A <;> aesop
    have hv : B ∪ (x.2 \ B) = x.2 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hi | hi)
        · exact hBX hi
        · exact hi.1
      · intro hi
        by_cases hb : i ∈ B <;> aesop
    have hcU : (x.1 \ A).card = w - A.card := by
      rw [Finset.card_sdiff hAX, hwA]
    have hcV : (x.2 \ B).card = w - B.card := by
      rw [Finset.card_sdiff hBX, hwB]
    have hAw : A.card ≤ w := by
      have := Finset.card_le_card hAX
      omega
    have hBw : B.card ≤ w := by
      have := Finset.card_le_card hBX
      omega
    apply Finset.mem_image.mpr
    refine ⟨(x.1 \ A, x.2 \ B), ?_, ?_⟩
    · apply (M7.PrefixSector.completion_membership N w E A B WA WB _).mpr
      refine ⟨_, hs, ?_⟩
      simp [M5.ConditionalCount.validCompletions, Finset.mem_powersetCard,
        hU, hV, hcU, hcV, hAw, hBw, hu, hv, hwA, hwB, hg]
    · simpa only [hu, hv] using (Prod.eta x)
