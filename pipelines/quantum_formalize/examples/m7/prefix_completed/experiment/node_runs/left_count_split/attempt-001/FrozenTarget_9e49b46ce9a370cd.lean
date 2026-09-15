import M7PrefixCompleted

theorem M7.PrefixCompleted.completed_membership : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint A WA → Disjoint B WB → ∀ x, x ∈ M7.PrefixCompleted.completed N w E A B WA WB ↔ M7.PrefixCompleted.Within A B WA WB x ∧ M7.PrefixCompleted.Valid N w E x := by
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

theorem M7.PrefixCompleted.left_children : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), ∀ i ∈ WA, M7.PrefixCompleted.Base N A B WA WB → M7.PrefixCompleted.Base N A B (WA.erase i) WB ∧ M7.PrefixCompleted.Base N (insert i A) B (WA.erase i) WB := by
  classical
  intro N w E A B WA WB i hi h
  unfold M7.PrefixCompleted.Base at h ⊢
  rcases h with ⟨hA0, hB0, hA, hB, hWA, hWB, hDA, hDB⟩
  have hErase : WA.erase i ⊆ Finset.range N := by
    intro a ha
    exact hWA (Finset.mem_of_mem_erase ha)
  have hDisj : Disjoint A (WA.erase i) := by
    apply Finset.disjoint_left.mpr
    intro a ha hw
    exact Finset.disjoint_left.mp hDA ha (Finset.mem_of_mem_erase hw)
  constructor
  · exact ⟨hA0, hB0, hA, hB, hErase, hWB, hDisj, hDB⟩
  · refine ⟨Finset.mem_insert_of_mem hA0, hB0, ?_, hB, hErase, hWB, ?_, hDB⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hWA hi
      · exact hA ha
    · apply Finset.disjoint_left.mpr
      intro a ha hw
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact (Finset.mem_erase.mp hw).1 rfl
      · exact Finset.disjoint_left.mp hDisj ha hw

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

theorem M7.PrefixCompleted.count_completed : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M7.PrefixCompleted.Base N A B WA WB → M7.PrefixSector.count N w E A B WA WB = (M7.PrefixCompleted.completed N w E A B WA WB).card := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M7.PrefixCompleted.Base N A B WA WB → M7.PrefixSector.count N w E A B WA WB = (M7.PrefixCompleted.completed N w E A B WA WB).card
  )
  change QuantumHarnessFrozenTarget
  classical
  unfold QuantumHarnessFrozenTarget
  intro N w E A B WA WB hN hE hBase
  by_cases hOver : w < A.card ∨ w < B.card
  · rw [M7.PrefixSector.overfull_zero N w E A B WA WB hOver,
      M7.PrefixCompleted.overfull_empty N w E A B WA WB hOver]
    simp
  · have hAw : A.card ≤ w := by omega
    have hBw : B.card ≤ w := by omega
    obtain ⟨hA0, hB0, hAN, hBN, hWAN, hWBN, hDA, hDB⟩ := hBase
    have hOK : M5.ConditionalCount.PrefixOK N w A B WA WB := by
      unfold M5.ConditionalCount.PrefixOK
      aesop
    rw [M7.PrefixSector.exact_sector_count N w E A B WA WB hN hE hOK]
    unfold M7.PrefixCompleted.completed
    rw [Finset.card_image_of_injOn
      (M7.PrefixCompleted.union_injective N w E A B WA WB hDA hDB)]

theorem M7.PrefixCompleted.left_disjoint : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint A WA → Disjoint B WB → ∀ i ∈ WA, Disjoint (M7.PrefixCompleted.completed N w E A B (WA.erase i) WB) (M7.PrefixCompleted.completed N w E (insert i A) B (WA.erase i) WB) := by
  classical
  intro N w E A B WA WB hDA hDB i hi
  have hD0 : Disjoint A (WA.erase i) :=
    hDA.mono_right (Finset.erase_subset i WA)
  have hD1 : Disjoint (insert i A) (WA.erase i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (Finset.mem_erase.mp hk).1 rfl
    · exact Finset.disjoint_left.mp hDA hj (Finset.mem_erase.mp hk).2
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨⟨hAX, hXA, hBX, hXB⟩, hv⟩ :=
    (M7.PrefixCompleted.completed_membership N w E A B (WA.erase i) WB hD0 hDB x).mp hx
  obtain ⟨⟨hIX, hXI, hBX', hXB'⟩, hv'⟩ :=
    (M7.PrefixCompleted.completed_membership N w E (insert i A) B (WA.erase i) WB hD1 hDB x).mp hy
  have hiX : i ∈ x.1 := hIX (Finset.mem_insert_self i A)
  rcases Finset.mem_union.mp (hXA hiX) with hiA | hiW
  · exact Finset.disjoint_left.mp hDA hiA hi
  · exact (Finset.mem_erase.mp hiW).1 rfl

theorem M7.PrefixCompleted.left_sets : ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), Disjoint A WA → Disjoint B WB → ∀ i ∈ WA, M7.PrefixCompleted.completed N w E A B WA WB = M7.PrefixCompleted.completed N w E A B (WA.erase i) WB ∪ M7.PrefixCompleted.completed N w E (insert i A) B (WA.erase i) WB := by
  classical
  intro N w E A B WA WB hDA hDB i hi
  have hDE : Disjoint A (WA.erase i) := hDA.mono_right (Finset.erase_subset i WA)
  have hDI : Disjoint (insert i A) (WA.erase i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (Finset.mem_erase.mp hk).1 rfl
    · exact Finset.disjoint_left.mp hDA hj (Finset.mem_erase.mp hk).2
  have hUnion : insert i A ∪ WA.erase i = A ∪ WA := by
    ext j
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    by_cases h : j = i <;> simp_all
  apply Finset.ext
  intro x
  rw [Finset.mem_union,
    M7.PrefixCompleted.completed_membership N w E A B WA WB hDA hDB x,
    M7.PrefixCompleted.completed_membership N w E A B (WA.erase i) WB hDE hDB x,
    M7.PrefixCompleted.completed_membership N w E (insert i A) B (WA.erase i) WB hDI hDB x]
  unfold M7.PrefixCompleted.Within
  constructor
  · rintro ⟨⟨hAX, hXA, hBX, hXB⟩, hv⟩
    by_cases hx : i ∈ x.1
    · right
      refine ⟨⟨?_, ?_, hBX, hXB⟩, hv⟩
      · exact Finset.insert_subset_iff.mpr ⟨hx, hAX⟩
      · simpa only [hUnion] using hXA
    · left
      refine ⟨⟨hAX, ?_, hBX, hXB⟩, hv⟩
      intro j hj
      rcases Finset.mem_union.mp (hXA hj) with ha | hw
      · exact Finset.mem_union.mpr (Or.inl ha)
      · apply Finset.mem_union.mpr
        right
        apply Finset.mem_erase.mpr
        refine ⟨?_, hw⟩
        intro hji
        subst j
        exact hx hj
  · rintro (⟨⟨hAX, hXA, hBX, hXB⟩, hv⟩ | ⟨⟨hAX, hXA, hBX, hXB⟩, hv⟩)
    · refine ⟨⟨hAX, ?_, hBX, hXB⟩, hv⟩
      exact hXA.trans (Finset.union_subset_union (by rfl) (Finset.erase_subset i WA))
    · refine ⟨⟨?_, ?_, hBX, hXB⟩, hv⟩
      · intro j hj
        exact hAX (Finset.mem_insert.mpr (Or.inr hj))
      · simpa only [hUnion] using hXA
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (E : Finset M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → M7.PrefixSector.ValidSector N E → M7.PrefixCompleted.Base N A B WA WB → ∀ i ∈ WA, M7.PrefixSector.count N w E A B WA WB = M7.PrefixSector.count N w E A B (WA.erase i) WB + M7.PrefixSector.count N w E (insert i A) B (WA.erase i) WB
