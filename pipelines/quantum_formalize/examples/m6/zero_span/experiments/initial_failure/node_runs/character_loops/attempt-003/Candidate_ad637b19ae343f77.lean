import FrozenTarget_ad637b19ae343f77
theorem M6.ZeroSpan.character_loops : QuantumHarnessFrozenTarget := by
  intro N hN i m n
  classical
  have heq : ∀ a b : M6.Transfer.Memory 0, (a = b) ↔ True := by
    intro a b
    exact iff_true_intro (Subsingleton.elim a b)
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    decide
  have hout : ∀ t : ZMod 2,
      M6.Transfer.localOutput (M6.ActualTransfer.window 0 1) m t = t := by
    intro t
    simp [M6.Transfer.localOutput, M6.ActualTransfer.window, Fin.sum_univ_succ]
    <;> rfl
  simp [M6.Transfer.edgeMatrix, heq, M6.ActualTransfer.characterWeight,
    hout, M6.Character.free_character_factor, hu, M6.Character.sign]
  <;> ring
