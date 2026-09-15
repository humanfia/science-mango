import FrozenTarget_e13fdea914eda32d
theorem M7.PrefixSector.leaf_zero_one : QuantumHarnessFrozenTarget := by
  classical
  intro N w E A B hN hE hPrefix
  rw [M7.PrefixSector.exact_sector_count N w E A B ∅ ∅ hN hE hPrefix]
  have hleaf : M7.PrefixSector.completions N w E A B ∅ ∅ =
      ({(∅, ∅)} : Finset (Finset ℕ × Finset ℕ)).filter (fun _ =>
        A.card = w ∧ B.card = w ∧
        M5.Connectivity.supportGcd N A B = 1 ∧
        M5.completeSignature (M5.SupportPolynomial.ofSupport A)
          (M5.SupportPolynomial.ofSupport B) N ∈ E) := by
    have hp := hPrefix
    unfold M5.ConditionalCount.PrefixOK at hp
    ext ⟨U, V⟩
    simp [M7.PrefixSector.completions, M5.ConditionalCount.validCompletions,
      Finset.mem_powersetCard, Finset.mem_product, and_assoc]
    <;> aesop (config := { terminal := false })
    <;> omega
  rw [hleaf]
  by_cases h : A.card = w ∧ B.card = w ∧
      M5.Connectivity.supportGcd N A B = 1 ∧
      M5.completeSignature (M5.SupportPolynomial.ofSupport A)
        (M5.SupportPolynomial.ofSupport B) N ∈ E
  <;> simp [h]
