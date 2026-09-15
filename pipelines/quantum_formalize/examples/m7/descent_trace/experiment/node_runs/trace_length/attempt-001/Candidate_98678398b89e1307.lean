import FrozenTarget_98678398b89e1307
theorem M7.DescentTrace.trace_length : QuantumHarnessFrozenTarget := by
  change ∀ (c : List Bool → ℤ) (p : List Bool) (n : ℕ), (M7.DescentTrace.trace c p n).length = n
  intro c p n
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      simp only [M7.DescentTrace.trace, List.length_cons, ih]
