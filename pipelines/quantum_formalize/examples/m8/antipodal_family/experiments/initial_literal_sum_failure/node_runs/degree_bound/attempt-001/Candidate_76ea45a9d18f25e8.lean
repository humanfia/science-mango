import FrozenTarget_76ea45a9d18f25e8
theorem M8.AntipodalFamily.degree_bound : QuantumHarnessFrozenTarget := by
  intro N inst hN hEven
  obtain ⟨hm, hne_one, hne_zero, hd⟩ := M8.AntipodalFamily.nontrivial N hN hEven
  rw [Polynomial.degree_eq_natDegree hne_zero, hd]
  exact_mod_cast (show N / 2 + 1 < N by omega)
