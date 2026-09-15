import FrozenTarget_0126730b463f20b1
theorem M6.Transfer.matrix_trace_cycle : QuantumHarnessFrozenTarget := by
  classical
  intro S K _ _ _ N _ A
  have hsnoc (k : ℕ) (F : (Fin (k + 1) → S) → K) :
      (∑ f, F f) = ∑ f : Fin k → S, ∑ x : S, F (Fin.snoc f x) := by
    let e : ((Fin k → S) × S) ≃ (Fin (k + 1) → S) :=
      { toFun := fun p => Fin.snoc p.1 p.2
        invFun := fun f => (fun i => f i.castSucc, f (Fin.last k))
        left_inv := by intro p; simp
        right_inv := by
          intro f
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp
          · simp }
    have he := Fintype.sum_equiv e
      (fun p => F (Fin.snoc p.1 p.2)) F (fun p => rfl)
    rw [← he, Fintype.sum_prod_type]
  have hexpand (n : ℕ) (B : Matrix S S K) :
      Matrix.trace (M6.Transfer.matrixProduct A n * B) =
        ∑ m : Fin (n + 1) → S,
          (∏ i : Fin n, A i.val (m i.castSucc) (m i.succ)) *
            B (m (Fin.last n)) (m 0) := by
    induction n generalizing B with
    | zero =>
        rw [hsnoc]
        simp [M6.Transfer.matrixProduct, Matrix.trace, Matrix.diag]
    | succ n ih =>
        rw [M6.Transfer.matrixProduct, Matrix.mul_assoc, ih]
        simp_rw [Matrix.mul_apply, Finset.mul_sum]
        rw [hsnoc]
        apply Finset.sum_congr rfl
        intro m _
        apply Finset.sum_congr rfl
        intro x _
        rw [Fin.prod_univ_castSucc]
        have hz : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
        have hs (i : Fin n) : i.castSucc.succ = i.succ.castSucc := rfl
        simp only [Fin.val_castSucc, hs, Fin.snoc_castSucc, Fin.val_last,
          Fin.snoc_last, hz]
        rfl
  have hN : N ≠ 0 := NeZero.ne N
  cases N with
  | zero => exact (hN rfl).elim
  | succ n =>
      have hc (i : Fin n) : i.castSucc + 1 = i.succ := by
        apply Fin.ext
        have h1 : 1 < n + 1 := by omega
        have hi : i.val + 1 < n + 1 := by omega
        simp [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt h1,
          Nat.mod_eq_of_lt hi]
      have hl : (Fin.last n : Fin (n + 1)) + 1 = 0 := by
        cases n with
        | zero => exact Subsingleton.elim _ _
        | succ n =>
            apply Fin.ext
            have h1 : 1 < n + 1 + 1 := by omega
            simp [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt h1]
      change Matrix.trace (M6.Transfer.matrixProduct A (n + 1)) =
        ∑ m : Fin (n + 1) → S,
          ∏ i : Fin (n + 1), A i.val (m i) (m (i + 1))
      rw [M6.Transfer.matrixProduct, hexpand]
      apply Finset.sum_congr rfl
      intro m _
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, hc, hl]
