import FrozenTarget_b4f9ba6d559086f5
theorem M8.Diagonal.delta_weight : QuantumHarnessFrozenTarget := by
  intro N inst j
  classical
  change (Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0)).card = 1
  have h : Finset.univ.filter (fun i : ZMod N => M6.Physical.delta N j i ≠ 0) = {j} := by
    ext i
    by_cases hij : i = j
    · subst i
      simp [M6.Physical.delta]
    · simp [M6.Physical.delta, hij, Ne.symm hij]
  rw [h]
  simp
