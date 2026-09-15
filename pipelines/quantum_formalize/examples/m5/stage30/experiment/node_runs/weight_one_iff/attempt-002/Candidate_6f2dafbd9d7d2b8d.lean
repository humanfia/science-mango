import FrozenTarget_6f2dafbd9d7d2b8d
theorem M5.OrderBoundary.weight_one_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), M5.PhysicalOrder.realizes N 1 F A B ↔ N = 1 ∧ F = 1 ∧ A = {0} ∧ B = {0}
  intro N F A B
  constructor
  · intro h
    unfold M5.PhysicalOrder.realizes at h
    have hAc : A.card = 1 := by tauto
    have hBc : B.card = 1 := by tauto
    have hAz : 0 ∈ A := by tauto
    have hBz : 0 ∈ B := by tauto
    have hA : A = {0} := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hAc
      rw [ha] at hAz
      have hz : 0 = a := Finset.mem_singleton.mp hAz
      simpa only [← hz] using ha
    have hB : B = {0} := by
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hBc
      rw [hb] at hBz
      have hz : 0 = b := Finset.mem_singleton.mp hBz
      simpa only [← hz] using hb
    subst A
    subst B
    simp_all [M5.Connectivity.supportGcd, M5.SupportPolynomial.ofSupport, M5.completeSignature]
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [M5.PhysicalOrder.realizes, M5.Connectivity.supportGcd, M5.SupportPolynomial.ofSupport, M5.completeSignature]
