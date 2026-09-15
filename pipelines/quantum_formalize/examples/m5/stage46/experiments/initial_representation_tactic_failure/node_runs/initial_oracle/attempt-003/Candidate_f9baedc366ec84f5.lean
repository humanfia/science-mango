import FrozenTarget_f9baedc366ec84f5
theorem M5.PhysicalRecovery.initial_oracle : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.PhysicalRecovery.oracle N w F [] = M5.OrderCount.C N w F
  intro N w F hN hw hF hFN
  classical
  have hselected (offset : ℕ) : M5.PhysicalRecovery.selected N offset [] = {0} := by
    simp [M5.PhysicalRecovery.selected]
  have havailable (offset : ℕ) : M5.PhysicalRecovery.available N offset [] = M5.OrderCount.positivePositions N := by
    ext x
    simp only [M5.PhysicalRecovery.available, M5.OrderCount.positivePositions,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range, List.length_nil]
    constructor <;> intro hx
    all_goals
      aesop (config := { terminal := false })
      all_goals first | omega | (refine ⟨x - 1, ?_⟩; omega)
  have hA : M5.PhysicalRecovery.selectedA N [] = {0} := hselected _
  have hB : M5.PhysicalRecovery.selectedB N [] = {0} := hselected _
  have hWA : M5.PhysicalRecovery.availableA N [] = M5.OrderCount.positivePositions N := havailable _
  have hWB : M5.PhysicalRecovery.availableB N [] = M5.OrderCount.positivePositions N := havailable _
  have hs := M5.PhysicalRecovery.state_domains N [] hN (by simp)
  simp only [M5.PhysicalRecovery.StateOK, hA, hB, hWA, hWB] at hs
  have hp : M5.ConditionalCount.PrefixOK N w {0} {0}
      (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) := by
    simp only [M5.ConditionalCount.PrefixOK, Finset.card_singleton]
    aesop (config := { terminal := false }) <;> omega
  have he := M5.ConditionalCount.exact_completion_C N w F {0} {0}
    (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N)
    hN hF hFN hp
  have hv : M5.ConditionalCount.validCompletions N w F {0} {0}
      (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) =
      M5.OrderCount.validPairs N w F := by
    simp [M5.ConditionalCount.validCompletions, M5.OrderCount.validPairs,
      Finset.singleton_union]
  rw [hv] at he
  rw [M5.OrderCount.exact_C N w F hN hw hF hFN]
  simpa [M5.PhysicalRecovery.oracle, hA, hB, hWA, hWB,
    Nat.succ_le_iff.mpr hw] using he
