import FrozenTarget_18aac87aed893b95
theorem M7.GenerationCalls.trace_count : QuantumHarnessFrozenTarget := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).2 = 2 * n
  intro c p n
  induction n generalizing p with
  | zero => simp [M7.GenerationCalls.traceMeasured]
  | succ n ih =>
      simp [M7.GenerationCalls.traceMeasured, ih, Nat.mul_succ, Nat.add_comm]
