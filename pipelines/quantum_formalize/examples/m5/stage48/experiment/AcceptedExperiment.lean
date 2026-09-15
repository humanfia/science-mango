import M5OriginalRootReady

theorem M5.Final.actual_order_recovery : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OrderRecoveryClause w F := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OrderRecoveryClause w F
  intro w F hw hmonic hcoeff
  unfold M5.Final.OrderRecoveryClause
  intro N hN hC
  classical
  have hdiv : F ∣ M5.cyclicModulus N := by
    by_cases hd : F ∣ M5.cyclicModulus N
    · exact hd
    · simp [M5.OrderCount.C, hd] at hC
  have hv := M5.PhysicalRecovery.recover_actual N w F hN hw hmonic hdiv hC
  unfold M5.PhysicalRecovery.wordValid at hv
  rcases hv with ⟨hlen, hs⟩
  constructor
  · simpa [M5.PhysicalRecovery.decisionCount] using hlen
  · unfold M5.PhysicalRecovery.ValidSupports at hs
    simp only [Finset.subset_iff, Finset.mem_range] at hs
    unfold M5.PhysicalOrder.realizes
    aesop

theorem M5.Final.actual_residue_recovery : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.ResidueRecoveryClause w F := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.ResidueRecoveryClause w F
  intro w F hw hmonic hcoeff
  unfold M5.Final.ResidueRecoveryClause
  exact M5.ArithmeticResidueRecovery.recovery_correct w F hw hmonic hcoeff

theorem M5.Final.original_m5 : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OriginalM5Spec w F := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.OriginalM5Spec w F
  intro w F hw hmonic hcoeff
  unfold M5.Final.OriginalM5Spec
  exact ⟨M5.Final.core w F hw hmonic hcoeff,
    M5.Final.actual_order_recovery w F hw hmonic hcoeff,
    fun _ => M5.Final.actual_residue_recovery w F hw hmonic hcoeff⟩
#print axioms M5.Final.actual_order_recovery
#print axioms M5.Final.actual_residue_recovery
#print axioms M5.Final.original_m5
