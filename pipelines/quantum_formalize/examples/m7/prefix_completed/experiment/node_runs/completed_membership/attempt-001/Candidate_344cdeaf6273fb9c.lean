import FrozenTarget_344cdeaf6273fb9c
theorem M7.PrefixCompleted.completed_membership : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B WA WB hDA hDB x
  change x ∈ (M7.PrefixSector.completions N w E A B WA WB).image (fun y => (A ∪ y.1, B ∪ y.2)) ↔ _
  constructor
  · intro hx
    obtain ⟨⟨U, V⟩, huv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨F, hFE, hF⟩ := (M7.PrefixSector.completion_membership N w E A B WA WB (U, V)).mp huv
    simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powersetCard, Prod.fst, Prod.snd] at hF
    have hU : U ⊆ WA := by aesop
    have hV : V ⊆ WB := by aesop
    have hdU : Disjoint A U := hDA.mono_right hU
    have hdV : Disjoint B V := hDB.mono_right hV
    have hcU := Finset.card_union_of_disjoint hdU
    have hcV := Finset.card_union_of_disjoint hdV
    constructor
    · change A ⊆ A ∪ U ∧ A ∪ U ⊆ A ∪ WA ∧ B ⊆ B ∪ V ∧ B ∪ V ⊆ B ∪ WB
      exact ⟨Finset.subset_union_left, Finset.union_subset_union (by rfl) hU,
        Finset.subset_union_left, Finset.union_subset_union (by rfl) hV⟩
    · change (A ∪ U).card = w ∧ (B ∪ V).card = w ∧ _
      refine ⟨by omega, by omega, ?_⟩
      aesop
  · rintro ⟨hWithin, hValid⟩
    rcases hWithin with ⟨hAX, hXA, hBX, hXB⟩
    rcases hValid with ⟨hcA, hcB, hg, hs⟩
    have hRA : x.1 \ A ⊆ WA := by
      intro i hi
      obtain ⟨hiX, hiA⟩ := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hXA hiX)).resolve_left hiA
    have hRB : x.2 \ B ⊆ WB := by
      intro i hi
      obtain ⟨hiX, hiB⟩ := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp (hXB hiX)).resolve_left hiB
    have hUA : A ∪ (x.1 \ A) = x.1 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hi | ⟨hi, _⟩)
        · exact hAX hi
        · exact hi
      · intro hi
        by_cases ha : i ∈ A
        · exact Or.inl ha
        · exact Or.inr ⟨hi, ha⟩
    have hUB : B ∪ (x.2 \ B) = x.2 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hi | ⟨hi, _⟩)
        · exact hBX hi
        · exact hi
      · intro hi
        by_cases hb : i ∈ B
        · exact Or.inl hb
        · exact Or.inr ⟨hi, hb⟩
    have hCA : (x.1 \ A).card = w - A.card := by
      rw [Finset.card_sdiff_of_subset hAX, hcA]
    have hCB : (x.2 \ B).card = w - B.card := by
      rw [Finset.card_sdiff_of_subset hBX, hcB]
    apply Finset.mem_image.mpr
    refine ⟨(x.1 \ A, x.2 \ B), ?_, ?_⟩
    · apply (M7.PrefixSector.completion_membership N w E A B WA WB _).mpr
      refine ⟨M5.completeSignature (M5.SupportPolynomial.ofSupport x.1) (M5.SupportPolynomial.ofSupport x.2) N, hs, ?_⟩
      simp [M5.ConditionalCount.validCompletions, hRA, hRB, hCA, hCB, hUA, hUB, hcA, hcB, hg]
    · simpa only [hUA, hUB] using (Prod.eta x)
