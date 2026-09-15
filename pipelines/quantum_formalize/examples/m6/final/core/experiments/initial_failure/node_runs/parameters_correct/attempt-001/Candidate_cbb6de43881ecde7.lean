import FrozenTarget_cbb6de43881ecde7
theorem M6.Final.parameters_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ParametersCorrect N a b
  intro N inst a b h
  unfold M6.Final.ParametersCorrect
  cases h
  repeat' first | assumption | (solve | exact?) | constructor
  all_goals first | omega | exact?
