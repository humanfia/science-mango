import FrozenTarget_38115ae494051d3f
theorem M6.Pinned.choose_properties : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ) (P : M6.Pinned.Pins m) (i : Fin m), M6.Pinned.refines P (M6.Pinned.choose c P i).1 ∧ (M6.Pinned.choose c P i).1 i ≠ none ∧ (M6.Pinned.choose c P i).2 ≤ 1
  intro m c P i
  cases h : P i with
  | none =>
      have hr (b : ZMod 2) : M6.Pinned.refines P (M6.Pinned.pin P i b) := by
        unfold M6.Pinned.refines
        intro j
        by_cases hj : j = i
        · subst j
          simp [h]
        · simp [M6.Pinned.pin, hj]
      have hn (b : ZMod 2) : M6.Pinned.pin P i b i ≠ none := by
        simp [M6.Pinned.pin]
      simp only [M6.Pinned.choose, h]
      split <;> simp_all
  | some b =>
      simp [M6.Pinned.choose, h, M6.Pinned.refines]
