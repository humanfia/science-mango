import FrozenTarget_eaf9fdfc677b552c
theorem M8.Diagonal.delta_weight : QuantumHarnessFrozenTarget := by
  intro N inst j
  classical
  unfold M6.Physical.weight
  have h : (Finset.univ.filter fun i : ZMod N => M6.Physical.delta N j i ≠ 0) = {j} := by
    ext i
    by_cases hij : i = j
    · subst i
      simp [M6.Physical.delta]
    · simp [M6.Physical.delta, hij, eq_comm]
  rw [h]
  simp
