import FrozenTarget_15b102c229ae99c6
theorem M5.ConditionalResidueCount.pair_indicator_exact : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), _
  intro T w F p q a b hT hF hFT
  have hg : 0 < M5.ConditionalResidueCount.selectedGcd T p q :=
    Nat.pos_of_dvd_of_pos
      ((M5.ConditionalResidueCount.prefix_gcd_divisibility T
        (M5.ConditionalResidueCount.selectedGcd T p q) p q).mp (dvd_refl _)).1 hT
  have hc := M5.Connectivity.connected_indicator
    (M5.ConditionalResidueCount.selectedGcd T p q)
    (insert 0 (Finset.univ.image (fun i => (a i).val)))
    (insert 0 (Finset.univ.image (fun i => (b i).val))) hg
  simp [M5.Connectivity.supportGcd, Finset.gcd_image] at hc
  have hp := M5.PolynomialIndicator.exact_signature_indicator
    (M5.ConditionalResidueCount.completedPolynomial
      (M5.ConditionalResidueCount.selectedPolynomial p) a)
    (M5.ConditionalResidueCount.completedPolynomial
      (M5.ConditionalResidueCount.selectedPolynomial q) b)
    F T hT hF hFT
  simp only [M5.ConditionalResidueCount.pairIndicator,
    M5.ConditionalResidueCount.feasibleIndicator,
    M5.ConditionalResidueCount.feasible]
  try dsimp only
  simp_all [M5.Connectivity.supportGcd, Finset.gcd_image,
    mul_ite, ite_mul]
  all_goals split_ifs <;> simp_all
