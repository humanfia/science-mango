import M5OrderBoundary

theorem M5.OrderBoundary.range_card : ∀ (S : Finset ℕ) (N : ℕ), (∀ e ∈ S, e < N) → S.card ≤ N := by
  change ∀ (S : Finset ℕ) (N : ℕ), (∀ e ∈ S, e < N) → S.card ≤ N
  intro S N h
  have hsub : S ⊆ Finset.range N := by
    intro e he
    exact Finset.mem_range.mpr (h e he)
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem M5.OrderBoundary.weight_one_iff : ∀ (N : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), M5.PhysicalOrder.realizes N 1 F A B ↔ N = 1 ∧ F = 1 ∧ A = {0} ∧ B = {0} := by
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

theorem M5.OrderBoundary.signature_lower_bounds : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F A B → M5.signaturePeriod F ∣ N ∧ w ≤ N ∧ F.natDegree < N := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F A B → M5.signaturePeriod F ∣ N ∧ w ≤ N ∧ F.natDegree < N
  intro N w F A B hmon hzero h
  unfold M5.PhysicalOrder.realizes at h
  have hA : ∀ e ∈ A, e < N := by tauto
  have hanchor : 0 ∈ A := by tauto
  have hcard : A.card = w := by tauto
  have hsig : M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) N = F := by tauto
  let a := M5.SupportPolynomial.ofSupport A
  let b := M5.SupportPolynomial.ofSupport B
  have hcyc : F ∣ M5.cyclicModulus N := by
    rw [← hsig]
    unfold M5.completeSignature
    first
    | exact EuclideanDomain.gcd_dvd_right (EuclideanDomain.gcd a b) (M5.cyclicModulus N)
    | exact dvd_trans (EuclideanDomain.gcd_dvd_right a (EuclideanDomain.gcd b (M5.cyclicModulus N))) (EuclideanDomain.gcd_dvd_right b (M5.cyclicModulus N))
  have hdiv : F ∣ a := by
    rw [← hsig]
    unfold M5.completeSignature
    first
    | exact dvd_trans (EuclideanDomain.gcd_dvd_left (EuclideanDomain.gcd a b) (M5.cyclicModulus N)) (EuclideanDomain.gcd_dvd_left a b)
    | exact EuclideanDomain.gcd_dvd_left a (EuclideanDomain.gcd b (M5.cyclicModulus N))
  have ha : a ≠ 0 := M5.SupportPolynomial.anchored_support_nonzero A hanchor
  have hdeg : a.natDegree < N := M5.SupportPolynomial.support_degree_bound A N (hA 0 hanchor) hA
  refine ⟨((M5.Period.period_law F hmon hzero).2 N).mp hcyc, ?_, ?_⟩
  · simpa only [hcard] using M5.OrderBoundary.range_card A N hA
  · exact lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hdiv ha) hdeg
#print axioms M5.OrderBoundary.range_card
#print axioms M5.OrderBoundary.signature_lower_bounds
#print axioms M5.OrderBoundary.weight_one_iff
