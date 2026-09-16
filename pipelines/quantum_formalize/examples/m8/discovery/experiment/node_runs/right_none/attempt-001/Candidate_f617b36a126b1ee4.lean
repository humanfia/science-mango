import FrozenTarget_f617b36a126b1ee4
theorem M8.Discovery.right_none : QuantumHarnessFrozenTarget := by
  classical
  intro N _ c e t a
  have hm (o : Option (Fin N × M8.Discovery.Choice N)) :
      o.map Prod.snd = none ↔ o = none := by
    cases o <;> simp
  rw [M8.Discovery.atRight, hm, M8.FiniteSearch.find_none]
  simp [M8.Discovery.test_spec]
