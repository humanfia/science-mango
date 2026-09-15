import FrozenTarget_9008a2e4d8a62450
theorem M6.ZeroSpan.character_loops : QuantumHarnessFrozenTarget := by
  classical
  intro N hN i m n
  have heq : ∀ a b : M6.Transfer.Memory 0, a = b ↔ True := by
    intro a b
    exact iff_true_intro (Subsingleton.elim a b)
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext t
    fin_cases t <;> simp
  have hout : ∀ t : ZMod 2, M6.Transfer.output (M6.ActualTransfer.window 0 1) m t = t := by
    intro t
    simp [M6.Transfer.output, M6.ActualTransfer.window]
  have hv : (1 : ZMod 2).val = 1 := rfl
  simp [M6.Transfer.edgeMatrix, heq, hu, M6.ActualTransfer.characterWeight,
    hout, M6.Character.free_character_factor, M6.Character.sign, hv]
  <;> ring
