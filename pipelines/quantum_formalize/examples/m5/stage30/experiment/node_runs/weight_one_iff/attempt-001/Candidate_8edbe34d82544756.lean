import FrozenTarget_8edbe34d82544756
theorem M5.OrderBoundary.weight_one_iff : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), M5.PhysicalOrder.realizes N 1 F A B ↔ N = 1 ∧ F = 1 ∧ A = {0} ∧ B = {0}
  intro N F A B
  classical
  constructor
  · intro h
    unfold M5.PhysicalOrder.realizes at h
    have hAc : A.card = 1 := by tauto
    have hBc : B.card = 1 := by tauto
    have hAz : 0 ∈ A := by tauto
    have hBz : 0 ∈ B := by tauto
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hAc
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hBc
    have ha : a = 0 := by simpa using hAz.symm
    have hb : b = 0 := by simpa using hBz.symm
    subst a
    subst b
    simp_all [M5.Connectivity.supportGcd, M5.SupportPolynomial.ofSupport,
      M5.completeSignature, EuclideanDomain.gcd]
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [M5.PhysicalOrder.realizes, M5.Connectivity.supportGcd,
      M5.SupportPolynomial.ofSupport, M5.completeSignature, EuclideanDomain.gcd]
