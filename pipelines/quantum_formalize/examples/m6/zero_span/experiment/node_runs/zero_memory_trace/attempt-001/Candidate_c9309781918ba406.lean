import FrozenTarget_c9309781918ba406
theorem M6.ZeroSpan.zero_memory_trace : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (W : ℕ → M6.Transfer.Memory 0 → M6.Transfer.Bit → Polynomial ℤ) (p : Polynomial ℤ), (∀ i m n, M6.Transfer.edgeMatrix (W i) m n = p) → M6.Transfer.arrayTrace W N = p ^ N
  intro N W p h
  classical
  haveI : Subsingleton (M6.Transfer.Memory 0) := ⟨fun a b => funext fun i => Fin.elim0 i⟩
  letI : Unique (M6.Transfer.Memory 0) :=
    { default := fun i => Fin.elim0 i
      uniq := fun m => Subsingleton.elim _ _ }
  have hp : ∀ n (m k : M6.Transfer.Memory 0),
      M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) n m k = p ^ n := by
    intro n
    induction n with
    | zero =>
        intro m k
        simp [M6.Transfer.matrixProduct, Matrix.one_apply, Subsingleton.elim m k]
    | succ n ih =>
        intro m k
        simp [M6.Transfer.matrixProduct, Matrix.mul_apply, ih, h, pow_succ, mul_comm]
  rw [M6.Transfer.array_trace_matrix 0 (Polynomial ℤ) W N]
  simp [Matrix.trace, Matrix.diag, hp]
