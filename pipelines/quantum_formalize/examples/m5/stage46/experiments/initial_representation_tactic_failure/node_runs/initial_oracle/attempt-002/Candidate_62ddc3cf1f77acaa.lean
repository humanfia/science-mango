import FrozenTarget_62ddc3cf1f77acaa
theorem M5.PhysicalRecovery.initial_oracle : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.PhysicalRecovery.oracle N w F [] = M5.OrderCount.C N w F
  intro N w F hN hw hF hFd
  classical
  have hs : ∀ offset, M5.PhysicalRecovery.selected N offset [] = {0} := by
    intro offset
    ext x
    simp [M5.PhysicalRecovery.selected]
    <;> aesop (config := { terminal := false }) <;> omega
  have ha : ∀ offset, M5.PhysicalRecovery.available N offset [] = M5.OrderCount.positivePositions N := by
    intro offset
    ext x
    simp [M5.PhysicalRecovery.available, M5.OrderCount.positivePositions]
    <;> aesop (config := { terminal := false }) <;> omega
  have hprefix : M5.ConditionalCount.PrefixOK N w {0} {0}
      (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) := by
    simp [M5.ConditionalCount.PrefixOK, M5.OrderCount.positivePositions,
      Finset.subset_iff]
    <;> omega
  have hc := M5.ConditionalCount.exact_completion_C N w F {0} {0}
    (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N)
    hN hF hFd hprefix
  have hp := M5.OrderCount.exact_C N w F hN hw hF hFd
  have he : M5.ConditionalCount.validCompletions N w F {0} {0}
      (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) =
      M5.OrderCount.validPairs N w F := by
    ext UV
    simp [M5.ConditionalCount.validCompletions, M5.OrderCount.validPairs,
      Finset.singleton_union]
    intro hU hcU hV hcV
    have hzU : 0 ∉ UV.1 := by
      intro hz
      have hh := hU hz
      simpa [M5.OrderCount.positivePositions] using hh
    have hzV : 0 ∉ UV.2 := by
      intro hz
      have hh := hV hz
      simpa [M5.OrderCount.positivePositions] using hh
    have hcU' : (insert 0 UV.1).card = w := by
      rw [Finset.card_insert_of_notMem hzU, hcU]
      omega
    have hcV' : (insert 0 UV.2).card = w := by
      rw [Finset.card_insert_of_notMem hzV, hcV]
      omega
    simp [hcU', hcV']
  rw [he] at hc
  simpa [M5.PhysicalRecovery.oracle, M5.PhysicalRecovery.selectedA,
    M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.availableA,
    M5.PhysicalRecovery.availableB, hs, ha] using hc.trans hp.symm
