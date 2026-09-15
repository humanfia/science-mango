import M6TransferTraceReady

theorem M6.Transfer.matrix_trace_cycle : ∀ (S K : Type) [Fintype S] [DecidableEq S] [CommSemiring K] (N : ℕ) [NeZero N] (A : ℕ → Matrix S S K), Matrix.trace (M6.Transfer.matrixProduct A N) = ∑ m : ZMod N → S, ∏ i : ZMod N, A i.val (m i) (m (i+1)) := by
  classical
  intro S K _ _ _ N _ A
  have sum_snoc (n : ℕ) (f : (Fin (n + 1) → S) → K) :
      (∑ m, f m) = ∑ m : Fin n → S, ∑ b : S, f (Fin.snoc m b) := by
    let e : ((Fin n → S) × S) ≃ (Fin (n + 1) → S) :=
      { toFun := fun p => Fin.snoc p.1 p.2
        invFun := fun m => (fun i => m i.castSucc, m (Fin.last n))
        left_inv := by intro p; simp
        right_inv := by
          intro m
          funext i
          cases i using Fin.lastCases <;> simp }
    calc
      (∑ m, f m) = ∑ p, f (e p) := (e.sum_comp f).symm
      _ = ∑ m : Fin n → S, ∑ b : S, f (Fin.snoc m b) := by
        change (∑ p : (Fin n → S) × S, f (Fin.snoc p.1 p.2)) = _
        exact Fintype.sum_prod_type (fun p : (Fin n → S) × S => f (Fin.snoc p.1 p.2))
  have expansion : ∀ n (B : Matrix S S K),
      Matrix.trace (M6.Transfer.matrixProduct A n * B) =
        ∑ m : Fin (n + 1) → S,
          (∏ i : Fin n, A i.val (m i.castSucc) (m i.succ)) *
            B (m (Fin.last n)) (m 0) := by
    intro n
    induction n with
    | zero =>
        intro B
        simpa [M6.Transfer.matrixProduct, Matrix.trace, Fin.snoc] using
          (sum_snoc 0 (fun m => B (m (Fin.last 0)) (m 0))).symm
    | succ n ih =>
        intro B
        rw [M6.Transfer.matrixProduct, Matrix.mul_assoc, ih]
        simp only [Matrix.mul_apply, Finset.mul_sum]
        conv_rhs => rw [sum_snoc (n + 1)]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro b _
        have hs (i : Fin n) :
            (Fin.snoc m b : Fin (n+2) → S) i.castSucc.succ = m i.succ := by
          exact Fin.snoc_castSucc (α := fun _ : Fin (n+2) => S) b m i.succ
        have hz : (Fin.snoc m b : Fin (n+2) → S) 0 = m 0 := by
          change (Fin.snoc m b : Fin (n+2) → S) (Fin.castSucc (0 : Fin (n + 1))) = m 0
          simp
        simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, Fin.val_castSucc, Fin.val_last, hs, hz, mul_assoc]
        congr 2
        congr 1
        exact (Fin.snoc_last (α := fun _ : Fin (n+2) => S) b m).symm
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [M6.Transfer.matrixProduct, expansion]
      change (∑ m : Fin (n + 1) → S,
        (∏ i : Fin n, A i.val (m i.castSucc) (m i.succ)) *
          A n (m (Fin.last n)) (m 0)) =
        ∑ m : Fin (n + 1) → S,
          ∏ i : Fin (n + 1), A i.val (m i) (m (i + 1))
      apply Finset.sum_congr rfl
      intro m _
      have hs (i : Fin n) : i.castSucc + 1 = i.succ := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one', Fin.val_castSucc, Fin.val_succ, Nat.add_mod_mod]
        exact Nat.mod_eq_of_lt i.succ.isLt
      have hl : (Fin.last n : Fin (n + 1)) + 1 = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one', Fin.val_last, Fin.val_zero, Nat.add_mod_mod]
        exact Nat.mod_self _
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hs, hl]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K), Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N) = ∑ p : M6.Transfer.ClosedWalk R N, ∏ i : ZMod N, W i.val (p.val.1 i) (M6.Transfer.labels p i)
