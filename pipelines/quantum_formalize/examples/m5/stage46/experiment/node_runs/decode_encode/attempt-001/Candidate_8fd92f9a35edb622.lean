import FrozenTarget_8fd92f9a35edb622
theorem M5.PhysicalRecovery.decode_encode : QuantumHarnessFrozenTarget := by
  classical
  intro N A B hN hA hB hA0 hB0
  have decode_block (offset : ℕ) (p : List Bool) (S : Finset ℕ)
      (hS : S ⊆ Finset.range N) (hS0 : 0 ∈ S)
      (hp : ∀ i < N - 1,
        (offset + i < p.length ∧ p[offset + i]? = some true) ↔ i + 1 ∈ S) :
      M5.PhysicalRecovery.selected N offset p = S := by
    ext s
    simp only [M5.PhysicalRecovery.selected, Finset.mem_insert,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hs
      rcases hs with hs | ⟨i, ⟨hi, hpi⟩, his⟩
      · subst s
        exact hS0
      · have hm := (hp i hi).mp hpi
        simpa only [his] using hm
    · intro hs
      by_cases hs0 : s = 0
      · exact Or.inl hs0
      · right
        have hsN : s < N := Finset.mem_range.mp (hS hs)
        have hi : s - 1 < N - 1 := by omega
        have he : s - 1 + 1 = s := by omega
        refine ⟨s - 1, ⟨hi, ?_⟩, he⟩
        apply (hp (s - 1) hi).mpr
        simpa only [he] using hs
  constructor
  · change M5.PhysicalRecovery.selected N 0 (M5.PhysicalRecovery.encode N A B) = A
    apply decode_block 0 (M5.PhysicalRecovery.encode N A B) A hA hA0
    intro i hi
    have hit : i < 2 * (N - 1) := by omega
    simp [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.decisionCount, hi, hit]
  · change M5.PhysicalRecovery.selected N (N - 1) (M5.PhysicalRecovery.encode N A B) = B
    apply decode_block (N - 1) (M5.PhysicalRecovery.encode N A B) B hB hB0
    intro i hi
    have hit : N - 1 + i < 2 * (N - 1) := by omega
    have hnot : ¬ N - 1 + i < N - 1 := by omega
    simp [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.decisionCount, hit, hnot]
