import FrozenTarget_12667eff93166868
theorem M6.ZeroSpan.boundary_loops : QuantumHarnessFrozenTarget := by
  classical
  intro N _ i m n
  have hs : ∀ t : M6.Transfer.Bit, M6.Transfer.shift m t = n := fun _ => Subsingleton.elim _ _
  have hu : (Finset.univ : Finset M6.Transfer.Bit) = {0, 1} := by decide
  simp only [M6.Transfer.edgeMatrix, hs, if_true, hu, Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton, zero_ne_one, not_false_eq_true]
  simp [M6.ActualTransfer.boundaryWeight, M6.ActualTransfer.window, M6.Character.boundaryFactor, M6.Pinned.free]
  first
  | simp [M6.Transfer.localOutput, M6.ActualTransfer.window, pow_two]
  | simp [M6.Transfer.output, M6.ActualTransfer.window, pow_two]
  all_goals norm_num [ZMod.val_one, pow_two]
