import FrozenTarget_1d37c9f55c85ad32
theorem M7.Selection.pareto_laws : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ), (∀ a : Fin m → ℤ, ¬ M7.Selection.pareto a a) ∧ (∀ a b c : Fin m → ℤ, M7.Selection.pareto a b → M7.Selection.pareto b c → M7.Selection.pareto a c)
  intro m
  constructor
  · intro a h
    unfold M7.Selection.pareto at h
    rcases h with ⟨_, i, hi⟩
    exact (lt_irrefl (a i)) hi
  · intro a b c hab hbc
    unfold M7.Selection.pareto at *
    rcases hab with ⟨hab, i, hi⟩
    rcases hbc with ⟨hbc, _⟩
    constructor
    · intro j
      have h₁ := hab j
      have h₂ := hbc j
      omega
    · refine ⟨i, ?_⟩
      have h₂ := hbc i
      omega
