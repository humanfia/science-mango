import FrozenTarget_17b6dabb42df9315
theorem M7.GenerationCalls.trace_projection : QuantumHarnessFrozenTarget := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.GenerationCalls.traceMeasured c p n).1 = M7.DescentTrace.trace c p n
  intro c p n
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      simp [M7.GenerationCalls.traceMeasured, M7.DescentTrace.trace, ih]
