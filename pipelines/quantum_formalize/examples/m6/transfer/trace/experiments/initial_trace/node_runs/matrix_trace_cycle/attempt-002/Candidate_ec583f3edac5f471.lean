import FrozenTarget_ec583f3edac5f471
theorem M6.Transfer.matrix_trace_cycle : QuantumHarnessFrozenTarget := by
  classical
  intro S K _ _ _ N _ A
  have sum_snoc (n : ℕ) (f : (Fin (n + 1) → S) → K) :
      ∑ m, f m = ∑ m : Fin n → S, ∑ b : S, f (Fin.snoc m b) := by
    let e : ((Fin n → S) × S) ≃ (Fin (n + 1) → S) :=
      { toFun := fun p => Fin.snoc p.1 p.2
        invFun := fun m => (fun i => m i.castSucc, m (Fin.last n))
        left_inv := by intro p; simp
        right_inv := by intro m; ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp }
    calc
      ∑ m, f m = ∑ p, f (e p) := (e.sum_comp f).symm
      _ = ∑ m : Fin n → S, ∑ b : S, f (Fin.snoc m b) :=
        Fintype.sum_prod_type' _
  have expansion (n : ℕ) (B : Matrix S S K) :
      Matrix.trace (M6.Transfer.matrixProduct A n * B) =
        ∑ m : Fin (n + 1) → S,
          (∏ i : Fin n, A i.val (m i.castSucc) (m i.succ)) *
            B (m (Fin.last n)) (m 0) := by
    induction n generalizing B with
    | zero =>
        rw [sum_snoc]
        simp [M6.Transfer.matrixProduct, Matrix.trace, Fin.snoc]
    | succ n ih =>
        rw [M6.Transfer.matrixProduct, Matrix.mul_assoc, ih, sum_snoc]
        simp_rw [Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro b hb
        have hs (i : Fin n) : i.castSucc.succ = i.succ.castSucc := rfl
        simp [Fin.prod_univ_castSucc, hs, mul_assoc]
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
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
      change ((i.val : ZMod (n + 1))).val = i.val
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
    have next (i : Fin n) : e i.castSucc + 1 = e i.succ := by
      change (i.val : ZMod (n + 1)) + 1 = ((i.val + 1 : ℕ) : ZMod (n + 1))
      simp
    have lastnext : e (Fin.last n) + 1 = e 0 := by
      change (n : ZMod (n + 1)) + ((1 : ℕ) : ZMod (n + 1)) = 0
      rw [← Nat.cast_add]
      exact ZMod.natCast_self (n + 1)
    let d : (Fin (n + 1) → S) ≃ (ZMod (n + 1) → S) :=
      { toFun := fun m i => m (e.symm i)
        invFun := fun m i => m (e i)
        left_inv := by intro m; funext i; simp
        right_inv := by intro m; funext i; simp }
    have de (m : Fin (n + 1) → S) (i : Fin (n + 1)) : d m (e i) = m i := by
      simp [d]
    change Matrix.trace (M6.Transfer.matrixProduct A n * A n) = _
    rw [expansion]
    rw [← d.sum_comp (fun m : ZMod (n + 1) → S =>
      ∏ i : ZMod (n + 1), A i.val (m i) (m (i + 1)))]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← e.prod_comp (fun i : ZMod (n + 1) =>
      A i.val (d m i) (d m (i + 1)))]
    rw [Fin.prod_univ_castSucc]
    simp only [eval, next, lastnext, de, Fin.val_castSucc, Fin.val_last]
