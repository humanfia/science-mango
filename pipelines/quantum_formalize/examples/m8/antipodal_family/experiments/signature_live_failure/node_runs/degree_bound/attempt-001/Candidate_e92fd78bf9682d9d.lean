import FrozenTarget_e92fd78bf9682d9d
theorem M8.AntipodalFamily.degree_bound : QuantumHarnessFrozenTarget := by
  intro N inst hN hEven
  obtain ⟨hm, hne_one, hne_zero, hd⟩ := M8.AntipodalFamily.nontrivial N hN hEven
  rw [Polynomial.degree_eq_natDegree hne_zero, hd]
  exact_mod_cast (show N / 2 + 1 < N by omega)
