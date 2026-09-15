import FrozenTarget_e6c7c5ff580810bb
theorem M5.TupleCharacter.character_tuple_sum : QuantumHarnessFrozenTarget := by
  change ∀ (D n k : ℕ) (f : Fin n → M5.Character.BinaryVector D) (t : Fin k → Fin n) (lam : M5.Character.BinaryVector D), M5.Character.value lam (M5.TupleCharacter.vectorSum f t) = ∏ i : Fin k, M5.Character.value lam (f (t i))
  intro D n k f t lam
  classical
  have h : ∀ s : Finset (Fin k), M5.Character.value lam (∑ i ∈ s, f (t i)) = ∏ i ∈ s, M5.Character.value lam (f (t i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty, Finset.prod_empty] using M5.TupleCharacter.value_zero D lam
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha]
        first
        | rw [M5.TupleCharacter.character_add]
        | rw [M5.Character.character_add]
        rw [ih]
  simpa [M5.TupleCharacter.vectorSum, Finset.sum_apply] using h Finset.univ
