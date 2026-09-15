import FrozenTarget_9ac0117e94912e63
theorem M5.PhysicalRecovery.initial_oracle : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.PhysicalRecovery.oracle N w F [] = M5.OrderCount.C N w F
  intro N w F hN hw hF hFN
  classical
  have hselected : ∀ offset, M5.PhysicalRecovery.selected N offset [] = {0} := by
    intro offset
    ext x
    simp [M5.PhysicalRecovery.selected]
    <;> aesop (config := { terminal := false }) <;> omega
  have havailable : ∀ offset, M5.PhysicalRecovery.available N offset [] = M5.OrderCount.positivePositions N := by
    intro offset
    ext x
    simp [M5.PhysicalRecovery.available, M5.OrderCount.positivePositions]
    <;> aesop (config := { terminal := false }) <;> omega
  have hA : M5.PhysicalRecovery.selectedA N [] = {0} := hselected _
  have hB : M5.PhysicalRecovery.selectedB N [] = {0} := hselected _
  have hWA : M5.PhysicalRecovery.availableA N [] = M5.OrderCount.positivePositions N := havailable _
  have hWB : M5.PhysicalRecovery.availableB N [] = M5.OrderCount.positivePositions N := havailable _
  have hs := M5.PhysicalRecovery.state_domains N [] hN (by simp)
  simp only [M5.PhysicalRecovery.StateOK, hA, hB, hWA, hWB] at hs
  have hp : M5.ConditionalCount.PrefixOK N w {0} {0} (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) := by
    simp only [M5.ConditionalCount.PrefixOK, Finset.card_singleton]
    aesop (config := { terminal := false }) <;> omega
  have he := M5.ConditionalCount.exact_completion_C N w F {0} {0} (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) hN hF hFN hp
  have hsets : M5.ConditionalCount.validCompletions N w F {0} {0} (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) = M5.OrderCount.validPairs N w F := by
    simp only [M5.ConditionalCount.validCompletions, M5.OrderCount.validPairs, Finset.card_singleton, Finset.singleton_union]
    apply Finset.filter_congr
    intro pair hpair
    obtain ⟨hU, hV⟩ := Finset.mem_product.mp hpair
    obtain ⟨hUs, hUc⟩ := Finset.mem_powersetCard.mp hU
    obtain ⟨hVs, hVc⟩ := Finset.mem_powersetCard.mp hV
    have hU0 : 0 ∉ pair.1 := by
      intro hz
      have hz' := hUs hz
      simpa [M5.OrderCount.positivePositions] using hz'
    have hV0 : 0 ∉ pair.2 := by
      intro hz
      have hz' := hVs hz
      simpa [M5.OrderCount.positivePositions] using hz'
    have hcU : (insert 0 pair.1).card = w := by
      rw [Finset.card_insert_of_notMem hU0, hUc]
      omega
    have hcV : (insert 0 pair.2).card = w := by
      rw [Finset.card_insert_of_notMem hV0, hVc]
      omega
    simp only [hcU, hcV, true_and]
  rw [hsets] at he
  have hc := M5.OrderCount.exact_C N w F hN hw hF hFN
  simpa [M5.PhysicalRecovery.oracle, hA, hB, hWA, hWB] using he.trans hc.symm
