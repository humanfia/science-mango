import FrozenTarget_ff1e50bd2fc1c35a
theorem M8.Discovery.none_iff : QuantumHarnessFrozenTarget := by
  classical
  intro N _ c
  have hm {m : ℕ} (o : Option (Fin m × M8.Discovery.Choice N)) :
      o.map Prod.snd = none ↔ o = none := by
    cases o <;> simp
  simp only [M8.Discovery.discover, M8.Discovery.atUnit,
    M8.Discovery.atLeft, hm, M8.FiniteSearch.find_none,
    M8.Discovery.right_none]
  constructor
  · intro h k
    rcases k with ⟨e, t, a, b⟩
    cases e
    · simpa using h (0 : Fin 2) t a b
    · simpa using h (1 : Fin 2) t a b
  · intro h e t a b
    exact h ⟨decide (e.val = 1), t, a, b⟩
