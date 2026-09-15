import M5OrderBoundary

theorem M5.OrderBoundary.range_card : ∀ (S : Finset ℕ) (N : ℕ), (∀ e ∈ S, e < N) → S.card ≤ N := by
  change ∀ (S : Finset ℕ) (N : ℕ), (∀ e ∈ S, e < N) → S.card ≤ N
  intro S N h
  have hsub : S ⊆ Finset.range N := by
    intro e he
    exact Finset.mem_range.mpr (h e he)
  simpa only [Finset.card_range] using Finset.card_le_card hsub
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (A B : Finset ℕ), F.Monic → F.coeff 0 = 1 → M5.PhysicalOrder.realizes N w F A B → M5.signaturePeriod F ∣ N ∧ w ≤ N ∧ F.natDegree < N
