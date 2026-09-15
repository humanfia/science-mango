import M6ZeroSpan

theorem M6.ZeroSpan.anchored_zero : ∀ (a b : M6.Final.BP), a.coeff 0 = 1 → b.coeff 0 = 1 → M6.ActualTransfer.span a b = 0 → a = 1 ∧ b = 1 := by
  change ∀ (a b : M6.Final.BP), a.coeff 0 = 1 → b.coeff 0 = 1 → M6.ActualTransfer.span a b = 0 → a = 1 ∧ b = 1
  intro a b ha hb hspan
  change max a.natDegree b.natDegree = 0 at hspan
  have hda : a.natDegree = 0 := by omega
  have hdb : b.natDegree = 0 := by omega
  constructor
  · simpa [ha] using (Polynomial.eq_C_of_natDegree_eq_zero hda)
  · simpa [hb] using (Polynomial.eq_C_of_natDegree_eq_zero hdb)

theorem M6.ZeroSpan.boundary_loops : ∀ (N : ℕ) [NeZero N] (i : ℕ) (m n : M6.Transfer.Memory 0), M6.Transfer.edgeMatrix (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N)) i) m n = (1 : Polynomial ℤ) + Polynomial.X^2 := by
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

theorem M6.ZeroSpan.signature_one : ∀ N : ℕ, M6.Cyclic.signature 1 1 (M6.Cyclic.modulus N) = 1 := by
  change ∀ N : ℕ, M6.Cyclic.signature 1 1 (M6.Cyclic.modulus N) = 1
  intro N
  simp [M6.Cyclic.signature]

theorem M6.ZeroSpan.zero_memory_trace : ∀ (N : ℕ) (W : ℕ → M6.Transfer.Memory 0 → M6.Transfer.Bit → Polynomial ℤ) (p : Polynomial ℤ), (∀ i m n, M6.Transfer.edgeMatrix (W i) m n = p) → M6.Transfer.arrayTrace W N = p^N := by
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

theorem M6.ZeroSpan.boundary_trace_zero : ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.boundaryTrace N 1 1 (M6.Pinned.free (2*N)) = ((1 : Polynomial ℤ) + Polynomial.X^2)^N := by
  change ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.boundaryTrace N 1 1 (M6.Pinned.free (2*N)) = ((1 : Polynomial ℤ) + Polynomial.X^2)^N
  intro N _
  classical
  have hs : M6.ActualTransfer.span 1 1 = 0 := by
    simp [M6.ActualTransfer.span]
  unfold M6.ActualTransfer.boundaryTrace
  rw [hs]
  trans M6.Transfer.arrayTrace (M6.ActualTransfer.boundaryWeight 0 N 1 1 (M6.Pinned.free (2*N))) N
  · apply M6.Transfer.scalar_trace_polynomial
    intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds (2*N) (M6.Pinned.free (2*N)) _ _ _ _).2
  · exact M6.ZeroSpan.zero_memory_trace N _ _ (M6.ZeroSpan.boundary_loops N)
#print axioms M6.ZeroSpan.anchored_zero
#print axioms M6.ZeroSpan.boundary_loops
#print axioms M6.ZeroSpan.signature_one
#print axioms M6.ZeroSpan.zero_memory_trace
#print axioms M6.ZeroSpan.boundary_trace_zero
