import FrozenTarget_fa3eeb104b96d6e0
theorem M6.ZeroSpan.character_loops : QuantumHarnessFrozenTarget := by
  intro N inst i m n
  classical
  have hm : ∀ a b : M6.Transfer.Memory 0, a = b := fun a b => Subsingleton.elim a b
  simp only [M6.Transfer.edgeMatrix, hm, if_true]
  simp only [M6.ActualTransfer.characterWeight, M6.Character.free_character_factor]
  change (∑ t : Fin 2, (1 + Polynomial.C (M6.Character.sign t) * Polynomial.X) * (1 + Polynomial.C (M6.Character.sign t) * Polynomial.X)) = _
  rw [Fin.sum_univ_two]
  norm_num [M6.Character.sign]
  ring
