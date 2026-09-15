import FrozenTarget_86ca5ff0bec99d0f
theorem M6.Euclid.preprocess_correct_cost : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (a b M : M6.Euclid.BP), a.natDegree ≤ N → b.natDegree ≤ N → M.natDegree ≤ N → (M6.Euclid.preprocess a b M).value = GCDMonoid.gcd (GCDMonoid.gcd a b) M ∧ M6.Euclid.preprocessBitCost N a b M ≤ 180 * (N + 1) ^ 3
  intro N a b M ha hb hM
  have hra : M6.Euclid.rank a ≤ N + 1 := by
    by_cases h : a = 0
    · simp [M6.Euclid.rank, h]
    · simp only [M6.Euclid.rank, h, ↓reduceIte]
      omega
  have hrb : M6.Euclid.rank b ≤ N + 1 := by
    by_cases h : b = 0
    · simp [M6.Euclid.rank, h]
    · simp only [M6.Euclid.rank, h, ↓reduceIte]
      omega
  have hr : M6.Euclid.rank (M6.Euclid.euclid a b).value ≤ N + 1 := by
    have hw := M6.Euclid.euclid_output_width (M6.Euclid.rank b + 1) a b
    simp only [M6.Euclid.euclid] at ⊢
    exact le_trans hw (max_le hra hrb)
  have hd : (M6.Euclid.euclid a b).value.natDegree ≤ N := by
    by_cases h : (M6.Euclid.euclid a b).value = 0
    · simp [h]
    · simp only [M6.Euclid.rank, h, ↓reduceIte] at hr
      omega
  refine ⟨?_, ?_⟩
  · have hv := (M6.Euclid.euclid_correct (M6.Euclid.euclid a b).value M).1
    rw [(M6.Euclid.euclid_correct a b).1] at hv
    simpa only [M6.Euclid.preprocess] using hv
  · have h₁ := (M6.Euclid.bit_cost_bound N a b ha hb).1
    have h₂ := (M6.Euclid.bit_cost_bound N (M6.Euclid.euclid a b).value M hd hM).1
    have heq : M6.Euclid.preprocessBitCost N a b M =
        M6.Euclid.bitCost N a b + M6.Euclid.bitCost N (M6.Euclid.euclid a b).value M := by
      simp only [M6.Euclid.preprocessBitCost, M6.Euclid.preprocess, M6.Euclid.bitCost] <;> ring
    rw [heq]
    omega
