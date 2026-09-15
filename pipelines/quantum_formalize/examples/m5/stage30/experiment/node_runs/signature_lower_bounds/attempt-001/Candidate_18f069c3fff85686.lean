import FrozenTarget_18f069c3fff85686
theorem M5.OrderBoundary.signature_lower_bounds : QuantumHarnessFrozenTarget := by
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
