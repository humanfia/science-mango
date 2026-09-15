import FrozenTarget_3883da6f275f9a5a
theorem M5.ConditionalResidueCount.pair_indicator_exact : QuantumHarnessFrozenTarget := by
  change ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (p q : List (Fin T)), ∀ a b, _
  intro T w F p q a b hT hF hFT
  classical
  have hg : 0 < M5.ConditionalResidueCount.selectedGcd T p q :=
    Nat.pos_of_dvd_of_pos
      ((M5.ConditionalResidueCount.prefix_gcd_divisibility T
        (M5.ConditionalResidueCount.selectedGcd T p q) p q).mp (dvd_refl _)).1 hT
  have hc := M5.Connectivity.connected_indicator
    (M5.ConditionalResidueCount.selectedGcd T p q)
    (insert 0 (Finset.univ.image (fun i => (a i).val)))
    (insert 0 (Finset.univ.image (fun i => (b i).val))) hg
  simp [M5.Connectivity.supportGcd, Finset.gcd_image, Function.comp_def] at hc
  have hs := M5.PolynomialIndicator.exact_signature_indicator
    (M5.ConditionalResidueCount.completedPolynomial
      (M5.ConditionalResidueCount.selectedPolynomial p) a)
    (M5.ConditionalResidueCount.completedPolynomial
      (M5.ConditionalResidueCount.selectedPolynomial q) b)
    F T hT hF hFT
  unfold M5.ConditionalResidueCount.pairIndicator
    M5.ConditionalResidueCount.feasibleIndicator
    M5.ConditionalResidueCount.feasible
  dsimp only
  rw [hc, hs]
  split_ifs <;> simp_all
