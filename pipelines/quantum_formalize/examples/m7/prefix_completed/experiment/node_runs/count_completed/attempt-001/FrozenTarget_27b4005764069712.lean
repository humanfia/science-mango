import M7PrefixCompleted

theorem M7.PrefixCompleted.overfull_empty : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), (w < A.card ∨ w < B.card) → M7.PrefixCompleted.completed N w E A B WA WB = ∅ := by
  classical
  intro N w E A B WA WB h
  apply Finset.ext
  intro y
  simp only [Finset.notMem_empty]
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨F, hF, hx⟩ := (M7.PrefixSector.completion_membership N w E A B WA WB x).mp hx
    have hA := Finset.card_le_card (Finset.subset_union_left : A ⊆ A ∪ x.1)
    have hB := Finset.card_le_card (Finset.subset_union_left : B ⊆ B ∪ x.2)
    unfold M5.ConditionalCount.validCompletions at hx
    simp_all [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] <;> omega
  · intro hy
    exact hy.elim

theorem M7.PrefixCompleted.union_injective : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint A WA → Disjoint B WB → Set.InjOn (fun x : Finset ℕ × Finset ℕ => (A ∪ x.1, B ∪ x.2)) (M7.PrefixSector.completions N w E A B WA WB : Set (Finset ℕ × Finset ℕ)) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint A WA → Disjoint B WB → Set.InjOn (fun x : Finset ℕ × Finset ℕ => (A ∪ x.1, B ∪ x.2)) (M7.PrefixSector.completions N w E A B WA WB : Set (Finset ℕ × Finset ℕ))
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro N w E A B WA WB hA hB
  have hsub : ∀ x ∈ M7.PrefixSector.completions N w E A B WA WB,
      x.1 ⊆ WA ∧ x.2 ⊆ WB := by
    intro x hx
    obtain ⟨F, hF, hx⟩ :=
      (M7.PrefixSector.completion_membership N w E A B WA WB x).mp hx
    simp only [M5.ConditionalCount.validCompletions, Finset.mem_filter,
      Finset.mem_product, Finset.mem_powersetCard] at hx
    aesop
  intro x hx y hy hxy
  have hsx := hsub x hx
  have hsy := hsub y hy
  have hAx : Disjoint A x.1 := hA.mono_right hsx.1
  have hAy : Disjoint A y.1 := hA.mono_right hsy.1
  have hBx : Disjoint B x.2 := hB.mono_right hsx.2
  have hBy : Disjoint B y.2 := hB.mono_right hsy.2
  apply Prod.ext
  · have h := congrArg (fun z : Finset ℕ × Finset ℕ => z.1 \ A) hxy
    simpa only [Finset.union_sdiff_cancel_left hAx,
      Finset.union_sdiff_cancel_left hAy] using h
  · have h := congrArg (fun z : Finset ℕ × Finset ℕ => z.2 \ B) hxy
    simpa only [Finset.union_sdiff_cancel_left hBx,
      Finset.union_sdiff_cancel_left hBy] using h
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M7.PrefixCompleted.Base N A B WA WB → M7.PrefixSector.count N w E A B WA WB = (M7.PrefixCompleted.completed N w E A B WA WB).card
