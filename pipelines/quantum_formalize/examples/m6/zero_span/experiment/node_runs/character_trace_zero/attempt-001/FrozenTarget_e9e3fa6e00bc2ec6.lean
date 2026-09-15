import M6ZeroSpan

theorem M6.ZeroSpan.character_loops : ∀ (N : ℕ) [NeZero N] (i : ℕ) (m n : M6.Transfer.Memory 0), M6.Transfer.edgeMatrix (M6.ActualTransfer.characterWeight 0 N 1 1 (M6.Pinned.free (2*N)) i) m n = Polynomial.C 2 * ((1 : Polynomial ℤ) + Polynomial.X^2) := by
  classical
  intro N hN i m n
  have heq : ∀ a b : M6.Transfer.Memory 0, a = b ↔ True := by
    intro a b
    exact iff_true_intro (Subsingleton.elim a b)
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    decide
  have hout : ∀ t : ZMod 2, M6.Transfer.output (M6.ActualTransfer.window 0 1) m t = t := by
    intro t
    simp [M6.Transfer.output, M6.ActualTransfer.window]
  have hv : (1 : ZMod 2).val = 1 := rfl
  simp [M6.Transfer.edgeMatrix, heq, hu, M6.ActualTransfer.characterWeight,
    hout, M6.Character.free_character_factor, M6.Character.sign, hv]
  <;> ring

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M6.ActualTransfer.characterTrace N 1 1 (M6.Pinned.free (2*N)) = Polynomial.C ((2 : ℤ)^N) * ((1 : Polynomial ℤ) + Polynomial.X^2)^N
