import FrozenTarget_6d3b07c326b47d3f
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
    have he : ∀ d : ℕ,
        d ∣ M5.ConditionalResidueCount.prefixGcd (p ++ List.ofFn a) ↔
        d ∣ Nat.gcd (M5.ConditionalResidueCount.prefixGcd p)
          (Finset.univ.gcd (fun i : Fin k => (a i).val)) := by
      intro d
      rw [hd, Nat.dvd_gcd_iff, hd, Finset.dvd_gcd_iff]
      constructor
      · intro h
        constructor
        · intro r hr
          exact h r (List.mem_append.mpr (Or.inl hr))
        · intro i hi
          apply h (a i)
          apply List.mem_append.mpr
          exact Or.inr (by simp)
      · rintro ⟨hp, ha⟩ r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hp r hr
        · have hi : ∃ i, a i = r := by simpa using hr
          rcases hi with ⟨i, rfl⟩
          exact ha i (Finset.mem_univ i)
    apply Nat.dvd_antisymm
    · exact (he _).mp dvd_rfl
    · exact (he _).mpr dvd_rfl
