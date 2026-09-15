import M5PhysicalOrder

theorem M5.PhysicalOrder.period_control : ∀ (A B : Finset ℕ) (w T : ℕ), 2 ≤ w → 0 < T → 0 ∈ A → 0 ∈ B → (∀ b ∈ B, b < w * T) → 0 < M5.PhysicalOrder.supportPeriod A B ∧ M5.PhysicalOrder.supportPeriod A B ≤ 2 ^ (w * T) ∧ EuclideanDomain.gcd (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) ∣ M5.cyclicModulus (M5.PhysicalOrder.supportPeriod A B) := by
  intro A B w T hw hT hA hB hBbound
  have hAc : (M5.SupportPolynomial.ofSupport A).coeff 0 = 1 := by
    simpa only [if_pos hA] using M5.SupportPolynomial.support_coeff_zero A
  have hBc : (M5.SupportPolynomial.ofSupport B).coeff 0 = 1 := by
    simpa only [if_pos hB] using M5.SupportPolynomial.support_coeff_zero B
  have hwT : 0 < w * T := Nat.mul_pos (by omega) hT
  have hdeg := M5.SupportPolynomial.support_degree_bound B (w * T) hwT hBbound
  have hb := M5.Signature.ordinary_gcd_period_bound (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) hAc hBc
  have hp := M5.Signature.ordinary_gcd_properties (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) hAc hBc
  unfold M5.PhysicalOrder.supportPeriod
  refine ⟨hb.1, le_trans hb.2 (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hdeg)), ?_⟩
  exact ((M5.Period.period_law _ hp.1 hp.2.1).2 _).mpr (dvd_refl _)

theorem M5.PhysicalOrder.literal_progression : ∀ (A B : Finset ℕ) (w T : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → 0 < T → A.card = w → B.card = w → 0 ∈ A → 0 ∈ B → (∀ a ∈ A, a < M5.packingCutoff w T) → (∀ b ∈ B, b < w * T) → M5.RepairSupport.combinedGcd A B = 1 → M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) T = F → ∀ j : ℕ, M5.packingCutoff w T ≤ T + j * M5.PhysicalOrder.supportPeriod A B → M5.PhysicalOrder.realizes (T + j * M5.PhysicalOrder.supportPeriod A B) w F A B := by
  intro A B w T F hw hT hAcard hBcard hA hB hAbound hBbound hg hF j hj
  have hcut : w * T < M5.packingCutoff w T := by
    unfold M5.packingCutoff
    nlinarith [Nat.mul_pos (by omega : 0 < w) hT]
  have hN : 0 < T + j * M5.PhysicalOrder.supportPeriod A B := by omega
  have hArange : ∀ a ∈ A, a < T + j * M5.PhysicalOrder.supportPeriod A B := by
    intro a ha
    exact lt_of_lt_of_le (hAbound a ha) hj
  have hBrange : ∀ b ∈ B, b < T + j * M5.PhysicalOrder.supportPeriod A B := by
    intro b hb
    exact lt_of_lt_of_le (lt_trans (hBbound b hb) hcut) hj
  have hconn : M5.Connectivity.supportGcd (T + j * M5.PhysicalOrder.supportPeriod A B) A B = 1 := by
    unfold M5.RepairSupport.combinedGcd at hg
    simpa [M5.Connectivity.supportGcd, Nat.gcd_assoc, hg]
  have hsig : M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) (T + j * M5.PhysicalOrder.supportPeriod A B) = F := by
    rw [M5.Signature.exact_signature_lift _ _ T (M5.PhysicalOrder.supportPeriod A B) j
      (M5.PhysicalOrder.period_control A B w T hw hT hA hB hBbound).2.2]
    exact hF
  unfold M5.PhysicalOrder.realizes
  simp_all only [Finset.subset_iff, Finset.mem_range]
  <;> aesop
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A B : Finset ℕ) (w T : ℕ) (F : M5.BinaryPolynomial), 2 ≤ w → 0 < T → A.card = w → B.card = w → 0 ∈ A → 0 ∈ B → (∀ a ∈ A, a < M5.packingCutoff w T) → (∀ b ∈ B, b < w * T) → M5.RepairSupport.combinedGcd A B = 1 → M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) T = F → ∃ N : ℕ, N < M5.birthBound w T ∧ M5.PhysicalOrder.realizes N w F A B
