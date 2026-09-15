import M6TransferTrace

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

theorem M6.Transfer.uniform_matrix_power : ∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (A : Matrix S S K) (N : ℕ), M6.Transfer.matrixProduct (fun _ => A) N = A ^ N := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (A : Matrix S S K) (N : ℕ), M6.Transfer.matrixProduct (fun _ => A) N = A ^ N
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro S K _ _ _ A N
  induction N with
  | zero => rfl
  | succ n ih =>
      simpa only [M6.Transfer.matrixProduct, pow_succ] using congrArg (fun B : Matrix S S K => B * A) ih

theorem M6.Transfer.array_trace_matrix : ∀ (R : ℕ) (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K) (N : ℕ), M6.Transfer.arrayTrace W N = Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N) := by
  classical
  intro R K inst W N
  change (∑ start : M6.Transfer.Memory R, M6.Transfer.layers W start N start) =
    ∑ start : M6.Transfer.Memory R, M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N start start
  apply Finset.sum_congr rfl
  intro start hstart
  exact M6.Transfer.layers_matrix R K W start start N
#print axioms M6.Transfer.layers_matrix
#print axioms M6.Transfer.array_trace_matrix
#print axioms M6.Transfer.uniform_matrix_power
