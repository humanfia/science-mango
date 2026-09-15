import FrozenTarget_0421d159b0a1f4b7
theorem M6.Pinned.enumerator_coeff : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), (M6.Pinned.enumerator L P).coeff d = M6.Pinned.count L P d
  intro m L P d
  classical
  simp only [M6.Pinned.enumerator, M6.Pinned.count,
    Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hrev : (d = M6.Pinned.weight v) ↔ (M6.Pinned.weight v = d) := eq_comm
  by_cases ha : M6.Pinned.agrees P v <;>
    by_cases hw : M6.Pinned.weight v = d <;>
    simp [ha, hw, Polynomial.coeff_X_pow, eq_comm]
  all_goals omega
