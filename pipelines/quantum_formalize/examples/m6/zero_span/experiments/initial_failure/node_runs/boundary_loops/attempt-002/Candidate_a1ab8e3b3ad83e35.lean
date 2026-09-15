import FrozenTarget_a1ab8e3b3ad83e35
theorem M6.ZeroSpan.boundary_loops : QuantumHarnessFrozenTarget := by
  intro N inst i m n
  classical
  have hs : ∀ t : M6.Transfer.Bit, M6.Transfer.shift m t = n := fun _ => Subsingleton.elim _ _
  simp only [M6.Transfer.edgeMatrix, hs, ite_true]
  change (∑ t : ZMod 2, M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2 * N)) i m t) = _
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton, zero_ne_one, not_false_eq_true]
  unfold M6.ActualTransfer.boundaryWeight
  first
  | simp [M6.Transfer.localOutput, M6.ActualTransfer.window, M6.Character.boundaryFactor, M6.Pinned.free, pow_two]
  | simp [M6.Transfer.output, M6.ActualTransfer.window, M6.Character.boundaryFactor, M6.Pinned.free, pow_two]
