import FrozenTarget_f6134dff7f006abf
theorem M5.ConditionalCount.selected_divisor_indicator : QuantumHarnessFrozenTarget := by
  intro N A B U V hN
  classical
  have hgN : M5.Connectivity.supportGcd N A B ∣ N :=
    ((M5.Connectivity.support_gcd_dvd N (M5.Connectivity.supportGcd N A B) A B).mp (dvd_refl _)).1
  have hgpos : 0 < M5.Connectivity.supportGcd N A B := by
    apply Nat.pos_of_ne_zero
    intro hz
    have : N = 0 := by simpa [hz] using hgN
    omega
  have hd : ∀ d : ℕ,
      d ∣ M5.Connectivity.supportGcd (M5.Connectivity.supportGcd N A B) U V ↔
      d ∣ M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) := by
    intro d
    simp only [M5.Connectivity.support_gcd_dvd, Finset.mem_union, or_imp, forall_and]
    tauto
  have heq : M5.Connectivity.supportGcd (M5.Connectivity.supportGcd N A B) U V =
      M5.Connectivity.supportGcd N (A ∪ U) (B ∪ V) := by
    apply Nat.dvd_antisymm
    · exact (hd _).mp (dvd_refl _)
    · exact (hd _).mpr (dvd_refl _)
  simpa only [M5.ConditionalCount.selectedDivisorSum, heq] using
    (M5.Connectivity.connected_indicator (M5.Connectivity.supportGcd N A B) U V hgpos)
