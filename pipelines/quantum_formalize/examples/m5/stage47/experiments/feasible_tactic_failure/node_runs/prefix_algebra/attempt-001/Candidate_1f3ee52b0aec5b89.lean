import FrozenTarget_1f3ee52b0aec5b89
theorem M5.ArithmeticResidueRecovery.prefix_algebra : QuantumHarnessFrozenTarget := by
  intro T k p a
  classical
  constructor
  · simp [M5.ConditionalResidueCount.selectedPolynomial,
      M5.ConditionalResidueCount.completedPolynomial,
      List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
      add_assoc]
  · have hd : ∀ (l : List (Fin T)) (d : ℕ),
        d ∣ M5.ConditionalResidueCount.prefixGcd l ↔ ∀ r ∈ l, d ∣ r.val := by
      intro l d
      induction l with
      | nil => simp [M5.ConditionalResidueCount.prefixGcd]
      | cons r l ih =>
        simp_all [M5.ConditionalResidueCount.prefixGcd, Nat.dvd_gcd_iff]
    have h : ∀ d : ℕ,
        d ∣ M5.ConditionalResidueCount.prefixGcd (p ++ List.ofFn a) ↔
        d ∣ Nat.gcd (M5.ConditionalResidueCount.prefixGcd p)
          (Finset.univ.gcd (fun i : Fin k => (a i).val)) := by
      intro d
      simp [Nat.dvd_gcd_iff, hd, Finset.dvd_gcd_iff, List.mem_ofFn]
    apply Nat.dvd_antisymm
    · exact (h _).mp (dvd_refl _)
    · exact (h _).mpr (dvd_refl _)
