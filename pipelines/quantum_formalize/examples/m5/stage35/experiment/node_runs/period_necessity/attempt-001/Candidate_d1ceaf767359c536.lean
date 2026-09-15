import FrozenTarget_d1ceaf767359c536
theorem M5.ResidueNecessity.period_necessity : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N w F A B hw hmonic hzero hphys
  obtain ⟨hT, hlaw⟩ := M5.Period.period_law F hmonic hzero
  have hsig : M5.completeSignature (M5.SupportPolynomial.ofSupport A)
      (M5.SupportPolynomial.ofSupport B) N = F := by
    unfold M5.PhysicalOrder.realizes at hphys
    tauto
  have hgcd (d x y : M5.BinaryPolynomial) :
      d ∣ EuclideanDomain.gcd x y ↔ d ∣ x ∧ d ∣ y := by
    constructor
    · intro h
      exact ⟨dvd_trans h (EuclideanDomain.gcd_dvd_left x y),
        dvd_trans h (EuclideanDomain.gcd_dvd_right x y)⟩
    · rintro ⟨hx, hy⟩
      exact EuclideanDomain.dvd_gcd hx hy
  have hFN : F ∣ M5.cyclicModulus N := by
    have h : F ∣ M5.completeSignature (M5.SupportPolynomial.ofSupport A)
        (M5.SupportPolynomial.ofSupport B) N := by
      rw [hsig]
    simp only [M5.completeSignature, hgcd] at h
    tauto
  exact M5.ResidueNecessity.physical_to_residue N w (M5.signaturePeriod F)
    F A B hw hT ((hlaw N).mp hFN)
    ((hlaw (M5.signaturePeriod F)).mpr (dvd_refl _)) hphys
