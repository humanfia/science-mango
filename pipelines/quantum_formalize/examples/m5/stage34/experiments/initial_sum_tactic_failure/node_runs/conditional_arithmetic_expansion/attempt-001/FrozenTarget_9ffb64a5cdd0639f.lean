import M5ConditionalCount

theorem M5.ConditionalCount.restricted_subset_domain : ∀ (W : Finset ℕ) (d k : ℕ), (M5.ConditionalCount.restricted W d).powersetCard k = (W.powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s) := by
  intro W d k
  classical
  change (W.filter (fun s => d ∣ s)).powersetCard k =
    (W.powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s)
  apply Finset.ext
  intro U
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hU, hk⟩
    refine ⟨⟨?_, hk⟩, ?_⟩
    · intro s hs
      exact (Finset.mem_filter.mp (hU hs)).1
    · intro s hs
      exact (Finset.mem_filter.mp (hU hs)).2
  · rintro ⟨⟨hU, hk⟩, hd⟩
    refine ⟨?_, hk⟩
    intro s hs
    exact Finset.mem_filter.mpr ⟨hU hs, hd s hs⟩

theorem M5.ConditionalCount.two_block_completion_count : ∀ (P : M5.BinaryPolynomial) (A B WA WB : Finset ℕ) (kA kB : ℕ), P.Monic → Disjoint A WA → Disjoint B WB → M5.ConditionalCount.nSelected P A WA kA * M5.ConditionalCount.nSelected P B WB kB = M5.ConditionalCount.twoBlockIndicatorSum P A B WA WB kA kB := by
  classical
  intro P A B WA WB kA kB hP hA hB
  simp only [M5.ConditionalCount.nSelected, dif_pos hP]
  rw [M5.CompletionBlock.completion_count P hP A WA kA hA,
    M5.CompletionBlock.completion_count P hP B WB kB hB]
  unfold M5.CompletionBlock.count M5.ConditionalCount.twoBlockIndicatorSum
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hUA : P ∣ M5.SupportPolynomial.ofSupport (A ∪ U) <;>
    by_cases hVB : P ∣ M5.SupportPolynomial.ofSupport (B ∪ V) <;>
    simp [hUA, hVB]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B WA WB : Finset ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → M5.ConditionalCount.PrefixOK N w A B WA WB → M5.ConditionalCount.rawCompletion N w F A B WA WB = ∑ U ∈ WA.powersetCard (w-A.card), ∑ V ∈ WB.powersetCard (w-B.card), M5.ConditionalCount.pairIndicator N F A B U V
