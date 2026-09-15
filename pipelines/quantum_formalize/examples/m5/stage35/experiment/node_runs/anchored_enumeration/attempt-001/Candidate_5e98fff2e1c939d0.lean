import FrozenTarget_5e98fff2e1c939d0
theorem M5.ResidueNecessity.anchored_enumeration : QuantumHarnessFrozenTarget := by
  change ∀ (A : Finset ℕ) (w : ℕ), 0 < w → A.card = w → 0 ∈ A → ∃ u : Fin w → ℕ, Function.Injective u ∧ Finset.univ.image u = A ∧ ∀ i : Fin w, i.val = 0 → u i = 0
  intro A w hw hcard hzero
  refine ⟨A.orderEmbOfFin hcard, (A.orderEmbOfFin hcard).injective, Finset.image_orderEmbOfFin_univ A hcard, ?_⟩
  intro i hi
  have hi' : i = ⟨0, hw⟩ := Fin.ext hi
  rw [hi', Finset.orderEmbOfFin_zero hcard hw]
  exact le_antisymm (Finset.min'_le A 0 hzero) (Nat.zero_le _)
