import FrozenTarget_27a8542faa71a635
theorem M6.Transfer.matrix_trace_cycle : QuantumHarnessFrozenTarget := by
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
          refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }
    rw [← Fintype.sum_prod_type]
    exact (Fintype.sum_equiv e _ _ (fun p => rfl)).symm
  have expansion (n : ℕ) (B : Matrix S S K) :
      Matrix.trace (M6.Transfer.matrixProduct A n * B) =
        ∑ m : Fin (n + 1) → S,
          (∏ i : Fin n, A i.val (m i.castSucc) (m i.succ)) *
            B (m (Fin.last n)) (m 0) := by
    induction n generalizing B with
    | zero =>
        rw [sum_snoc]
        simp [M6.Transfer.matrixProduct, Matrix.trace, Matrix.diag]
    | succ n ih =>
        rw [M6.Transfer.matrixProduct, Matrix.mul_assoc, ih]
        symm
        rw [sum_snoc (n + 1)]
        symm
        apply Finset.sum_congr rfl
        intro m hm
        rw [Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Fin.prod_univ_castSucc]
        simp [mul_assoc]
  cases N with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ n =>
      let e : Fin (n + 1) ≃ ZMod (n + 1) :=
        { toFun := fun i => (i.val : ZMod (n + 1))
          invFun := fun i => ⟨i.val, ZMod.val_lt i⟩
          left_inv := by
            intro i
            apply Fin.ext
            simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
          right_inv := by
            intro i
            exact ZMod.natCast_zmod_val i }
      have eval (i : Fin (n + 1)) : (e i).val = i.val := by
        simp [e, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
      have next (i : Fin n) : e i.castSucc + 1 = e i.succ := by
        change (i.val : ZMod (n + 1)) + 1 = ((i.val + 1 : ℕ) : ZMod (n + 1))
        simp
      have last_next : e (Fin.last n) + 1 = e 0 := by
        change (n : ZMod (n + 1)) + 1 = ((0 : ℕ) : ZMod (n + 1))
        rw [← Nat.cast_add, ZMod.natCast_self]
        simp
      let E : (Fin (n + 1) → S) ≃ (ZMod (n + 1) → S) :=
        { toFun := fun m i => m (e.symm i)
          invFun := fun m i => m (e i)
          left_inv := by intro m; funext i; simp
          right_inv := by intro m; funext i; simp }
      change Matrix.trace (M6.Transfer.matrixProduct A (n + 1)) = _
      rw [M6.Transfer.matrixProduct, expansion]
      apply Fintype.sum_equiv E
      intro m
      have reindex :
          (∏ i : Fin (n + 1), A i.val (m i) (E m (e i + 1))) =
            ∏ i : ZMod (n + 1), A i.val (E m i) (E m (i + 1)) := by
        apply Fintype.prod_equiv e
        intro i
        simp [E, eval]
      rw [← reindex, Fin.prod_univ_castSucc]
      simp [next, last_next, E]
