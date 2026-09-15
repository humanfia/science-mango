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

theorem M6.Transfer.array_trace_matrix : ∀ (R : ℕ) (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K) (N : ℕ), M6.Transfer.arrayTrace W N = Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N) := by
  classical
  intro R K inst W N
  change (∑ start : M6.Transfer.Memory R, M6.Transfer.layers W start N start) =
    ∑ start : M6.Transfer.Memory R, M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N start start
  apply Finset.sum_congr rfl
  intro start hstart
  exact M6.Transfer.layers_matrix R K W start start N

theorem M6.Transfer.labelled_trace : ∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K), Matrix.trace (M6.Transfer.matrixProduct (fun i => M6.Transfer.edgeMatrix (W i)) N) = ∑ p : M6.Transfer.ClosedWalk R N, ∏ i : ZMod N, W i.val (p.val.1 i) (M6.Transfer.labels p i) := by
  classical
  intro R N _ K _ W
  have hprod (m : ZMod N → M6.Transfer.Memory R) (h : M6.Transfer.Input N) :
      (∏ i : ZMod N, if M6.Transfer.shift (m i) (h i) = m (i + 1)
        then W i.val (m i) (h i) else 0) =
      if M6.Transfer.Follows R N m h then ∏ i : ZMod N, W i.val (m i) (h i) else 0 := by
    by_cases hf : M6.Transfer.Follows R N m h
    · rw [if_pos hf]
      apply Finset.prod_congr rfl
      intro i _
      exact if_pos (hf i).symm
    · rw [if_neg hf]
      unfold M6.Transfer.Follows at hf
      push_neg at hf
      obtain ⟨i, hi⟩ := hf
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact if_neg (Ne.symm hi)
  let T := (ZMod N → M6.Transfer.Memory R) × M6.Transfer.Input N
  let P : T → Prop := fun q => M6.Transfer.Follows R N q.1 q.2
  let f : T → K := fun q => ∏ i : ZMod N, W i.val (q.1 i) (q.2 i)
  rw [M6.Transfer.matrix_trace_cycle (M6.Transfer.Memory R) K N]
  simp only [M6.Transfer.edgeMatrix, Fintype.prod_sum]
  calc
    (∑ m : ZMod N → M6.Transfer.Memory R, ∑ h : M6.Transfer.Input N,
        ∏ i : ZMod N, if M6.Transfer.shift (m i) (h i) = m (i + 1)
          then W i.val (m i) (h i) else 0) =
        ∑ q : T, if P q then f q else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro h _
      exact hprod m h
    _ = ∑ q ∈ Finset.univ.filter P, f q := by
      rw [Finset.sum_filter]
    _ = ∑ p : M6.Transfer.ClosedWalk R N,
        ∏ i : ZMod N, W i.val (p.val.1 i) (M6.Transfer.labels p i) := by
      apply Finset.sum_bij
        (fun q hq => (⟨q, (Finset.mem_filter.mp hq).2⟩ : M6.Transfer.ClosedWalk R N))
      · intro q hq
        exact Finset.mem_univ _
      · intro a ha b hb hab
        exact congrArg Subtype.val hab
      · intro p hp
        exact ⟨p.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.property⟩, rfl⟩
      · intro q hq
        rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) [NeZero N] (K : Type) [CommSemiring K] (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → K), M6.Transfer.arrayTrace W N = ∑ h : M6.Transfer.Input N, ∏ i : ZMod N, W i.val (M6.Transfer.memoryAt h i) (h i)
