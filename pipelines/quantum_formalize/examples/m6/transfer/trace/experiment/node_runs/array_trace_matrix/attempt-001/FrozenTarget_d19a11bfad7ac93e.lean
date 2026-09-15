import M6TransferTraceReady

theorem M6.Transfer.layers_matrix : ∀ (R : ℕ) (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K) (start finish : M6.Transfer.Memory R) (n : ℕ), M6.Transfer.layers W start n finish = M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) n start finish := by
  classical
  intro R K inst W start finish n
  induction n generalizing finish with
  | zero =>
      simp [M6.Transfer.layers, M6.Transfer.matrixProduct, Matrix.one_apply, eq_comm]
  | succ n ih =>
      simp only [M6.Transfer.layers, M6.Transfer.propagate,
        M6.Transfer.matrixProduct, Matrix.mul_apply, M6.Transfer.edgeMatrix,
        Finset.mul_sum, mul_ite, mul_zero, ih]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R : ℕ) (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K) (N : ℕ), M6.Transfer.arrayTrace W N = Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N)
