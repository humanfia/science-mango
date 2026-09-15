import FrozenTarget_11b57a24dea9c202
theorem M6.ZeroSpan.zero_memory_trace : QuantumHarnessFrozenTarget := by
  classical
  intro N W p h
  haveI : Subsingleton (M6.Transfer.Memory 0) := ⟨by
    intro a b
    funext i
    exact Fin.elim0 i⟩
  have hu : (Finset.univ : Finset (M6.Transfer.Memory 0)) = {default} := by
    ext m
    simp [Subsingleton.elim m (default : M6.Transfer.Memory 0)]
  have hp : ∀ n (a b : M6.Transfer.Memory 0),
      M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) n a b = p ^ n := by
    intro n
    induction n with
    | zero =>
        intro a b
        simp [M6.Transfer.matrixProduct, Matrix.one_apply, Subsingleton.elim a b]
    | succ n ih =>
        intro a b
        simp [M6.Transfer.matrixProduct, Matrix.mul_apply, ih, h, hu, pow_succ, mul_comm]
  rw [M6.Transfer.array_trace_matrix 0 (Polynomial ℤ) W N]
  simp [Matrix.trace, Matrix.diag, hp, hu]
