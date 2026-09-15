import FrozenTarget_117967c821b9b26c
theorem M6.ZeroSpan.boundary_loops : QuantumHarnessFrozenTarget := by
  intro N inst i m n
  classical
  have hs (t : M6.Transfer.Bit) : M6.Transfer.shift m t = n := Subsingleton.elim _ _
  simp only [M6.Transfer.edgeMatrix, hs, if_true]
  change (∑ t : Fin 2, M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2 * N)) i m t) = _
  rw [Fin.sum_univ_two]
  first
  | simpa [M6.ActualTransfer.boundaryWeight, M6.ActualTransfer.window,
      M6.Character.boundaryFactor, M6.Pinned.free, M6.Transfer.output,
      Fin.sum_univ_succ, pow_two]
  | simpa [M6.ActualTransfer.boundaryWeight, M6.ActualTransfer.window,
      M6.Character.boundaryFactor, M6.Pinned.free, M6.Transfer.localOutput,
      Fin.sum_univ_succ, pow_two]
