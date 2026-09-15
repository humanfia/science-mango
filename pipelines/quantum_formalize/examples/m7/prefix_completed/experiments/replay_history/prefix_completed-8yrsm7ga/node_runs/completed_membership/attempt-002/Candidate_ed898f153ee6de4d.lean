import FrozenTarget_ed898f153ee6de4d
theorem M7.PrefixCompleted.completed_membership : QuantumHarnessFrozenTarget := by
  by
    classical
    change ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint A WA → Disjoint B WB → ∀ x, x ∈ M7.PrefixCompleted.completed N w E A B WA WB ↔ M7.PrefixCompleted.Within A B WA WB x ∧ M7.PrefixCompleted.Valid N w E x
    intro N w E A B WA WB hA hB x
    constructor
    · intro hx
      obtain ⟨⟨U, V⟩, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨F, hF, hy⟩ := (M7.PrefixSector.completion_membership N w E A B WA WB (U, V)).mp hy
      simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter] at hy
      rcases hy with ⟨hdom, hcA, hcB, hg, hs⟩
      have hU := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hdom).1).1
      have hV := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hdom).2).1
      constructor
      · change A ⊆ A ∪ U ∧ A ∪ U ⊆ A ∪ WA ∧ B ⊆ B ∪ V ∧ B ∪ V ⊆ B ∪ WB
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i hi
          exact Finset.mem_union.mpr (Or.inl hi)
        · intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact Finset.mem_union.mpr (Or.inl hi)
          · exact Finset.mem_union.mpr (Or.inr (hU hi))
        · intro i hi
          exact Finset.mem_union.mpr (Or.inl hi)
        · intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact Finset.mem_union.mpr (Or.inl hi)
          · exact Finset.mem_union.mpr (Or.inr (hV hi))
      · change (A ∪ U).card = w ∧ (B ∪ V).card = w ∧ M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) = 1 ∧ M5.completeSignature (M5.SupportPolynomial.ofSupport (A ∪ U)) (M5.SupportPolynomial.ofSupport (B ∪ V)) N ∈ E
        exact ⟨hcA, hcB, hg, hs ▸ hF⟩
    · rintro ⟨hwithin, hvalid⟩
      rcases x with ⟨X, Y⟩
      rcases hwithin with ⟨hAX, hX, hBY, hY⟩
      rcases hvalid with ⟨hwX, hwY, hg, hs⟩
      have hU : X \ A ⊆ WA := by
        intro i hi
        rcases Finset.mem_sdiff.mp hi with ⟨hiX, hiA⟩
        exact (Finset.mem_union.mp (hX hiX)).resolve_left hiA
      have hV : Y \ B ⊆ WB := by
        intro i hi
        rcases Finset.mem_sdiff.mp hi with ⟨hiY, hiB⟩
        exact (Finset.mem_union.mp (hY hiY)).resolve_left hiB
      have hu : A ∪ (X \ A) = X := by
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
      have hv : B ∪ (Y \ B) = Y := by
        ext i
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (hi | ⟨hi, _⟩)
          · exact hBY hi
          · exact hi
        · intro hi
          by_cases hb : i ∈ B
          · exact Or.inl hb
          · exact Or.inr ⟨hi, hb⟩
      have hcU : (X \ A).card = w - A.card := by
        rw [Finset.card_sdiff_of_subset hAX, hwX]
      have hcV : (Y \ B).card = w - B.card := by
        rw [Finset.card_sdiff_of_subset hBY, hwY]
      apply Finset.mem_image.mpr
      refine ⟨(X \ A, Y \ B), ?_, ?_⟩
      · apply (M7.PrefixSector.completion_membership N w E A B WA WB (X \ A, Y \ B)).mpr
        refine ⟨M5.completeSignature (M5.SupportPolynomial.ofSupport X) (M5.SupportPolynomial.ofSupport Y) N, hs, ?_⟩
        simp [M5.ConditionalCount.validCompletions, Finset.mem_powersetCard, hU, hV, hcU, hcV, hu, hv, hwX, hwY, hg]
      · exact Prod.ext hu hv
