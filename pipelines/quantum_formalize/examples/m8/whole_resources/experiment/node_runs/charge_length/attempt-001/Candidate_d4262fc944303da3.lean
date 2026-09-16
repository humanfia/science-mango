import FrozenTarget_d4262fc944303da3
theorem M8.WholeResources.charge_length : QuantumHarnessFrozenTarget := by
  intro N inst c
  classical
  unfold M8.WholeResources.run
  simp only
  split
  · simp only [List.length_cons, List.length_nil]
    omega
  · try simp only
    split
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · try simp only
      split
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
