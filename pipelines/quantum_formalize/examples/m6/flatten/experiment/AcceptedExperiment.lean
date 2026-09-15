import M6Flatten

theorem M6.Flatten.flatten_add : ∀ (N : ℕ) (z w : M6.Physical.Word N), M6.Flatten.flatten N (z+w) = M6.Flatten.flatten N z + M6.Flatten.flatten N w := by
  change ∀ (N : ℕ) (z w : M6.Physical.Word N), M6.Flatten.flatten N (z + w) = M6.Flatten.flatten N z + M6.Flatten.flatten N w
  intro N z w
  funext i
  by_cases h : i.val < N <;> simp [M6.Flatten.flatten, h]

theorem M6.Flatten.flatten_dot : ∀ (N : ℕ) [NeZero N] (z w : M6.Physical.Word N), M6.Character.dot (M6.Flatten.flatten N z) (M6.Flatten.flatten N w) = M6.Physical.pairing N z w := by
  change ∀ (N : ℕ) [NeZero N] (z w : M6.Physical.Word N), M6.Character.dot (M6.Flatten.flatten N z) (M6.Flatten.flatten N w) = M6.Physical.pairing N z w
  intro N inst z w
  classical
  let e : Fin N ≃ ZMod N :=
    { toFun := fun i => (i.val : ZMod N)
      invFun := fun i => ⟨i.val, ZMod.val_lt i⟩
      left_inv := by
        intro i
        apply Fin.ext
        change ((i.val : ZMod N).val) = i.val
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.is_lt]
      right_inv := by
        intro i
        simp }
  have hsum (f : ZMod N → ZMod 2) :
      (∑ i : Fin N, f (i.val : ZMod N)) = ∑ i : ZMod N, f i :=
    e.sum_comp f
  have hleft (i : Fin N) : i.val < N := i.is_lt
  have hright (i : Fin N) : ¬ N + i.val < N := by omega
  unfold M6.Character.dot M6.Flatten.flatten M6.Physical.pairing M6.Physical.dot
  rw [two_mul, Fin.sum_univ_add]
  simpa [Fin.val_castAdd, Fin.val_natAdd, hleft, hright] using
    congrArg₂ (fun a b : ZMod 2 => a + b)
      (hsum (fun i => z.1 i * w.1 i))
      (hsum (fun i => z.2 i * w.2 i))

theorem M6.Flatten.flatten_left : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Flatten.unflatten N (M6.Flatten.flatten N z) = z := by
  intro N _ z
  apply Prod.ext
  · funext i
    have hi : i.val < N := ZMod.val_lt i
    simp [M6.Flatten.unflatten, M6.Flatten.flatten, hi]
  · funext i
    have hi : ¬ N + i.val < N := by omega
    simp [M6.Flatten.unflatten, M6.Flatten.flatten, hi, Nat.add_sub_cancel_left]

theorem M6.Flatten.flatten_right : ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Flatten.flatten N (M6.Flatten.unflatten N v) = v := by
  change ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2 * N)), M6.Flatten.flatten N (M6.Flatten.unflatten N v) = v
  intro N inst v
  funext i
  by_cases h : i.val < N
  · simp only [M6.Flatten.flatten, M6.Flatten.unflatten, if_pos h, dif_pos h]
    apply congrArg v
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt h]
  · have hi : i.val - N < N := by omega
    simp only [M6.Flatten.flatten, M6.Flatten.unflatten, if_neg h, dif_neg h]
    apply congrArg v
    apply Fin.ext
    simp only [Fin.val_mk, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    omega

theorem M6.Flatten.flatten_smul : ∀ (N : ℕ) (c : ZMod 2) (z : M6.Physical.Word N), M6.Flatten.flatten N (c • z) = c • M6.Flatten.flatten N z := by
  change ∀ (N : ℕ) (c : ZMod 2) (z : M6.Physical.Word N), M6.Flatten.flatten N (c • z) = c • M6.Flatten.flatten N z
  intro N c z
  funext i
  simp only [M6.Flatten.flatten, Pi.smul_apply]
  split <;> simp_all

theorem M6.Flatten.flatten_weight : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Pinned.weight (M6.Flatten.flatten N z) = M6.Physical.wordWeight N z := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Pinned.weight (M6.Flatten.flatten N z) = M6.Physical.wordWeight N z
  intro N inst z
  classical
  have hs (f : ZMod N → ℕ) :
      (∑ i : Fin N, f (i.val : ZMod N)) = ∑ x : ZMod N, f x := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n =>
      change (∑ i : ZMod (n + 1), f (i.val : ZMod (n + 1))) = _
      apply Finset.sum_congr rfl
      intro i _
      rw [ZMod.natCast_zmod_val]
  unfold M6.Pinned.weight M6.Flatten.flatten M6.Physical.wordWeight M6.Physical.weight
  simp only [Finset.card_filter]
  rw [show 2 * N = N + N by omega, Fin.sum_univ_add]
  apply congrArg₂ (fun a b : ℕ => a + b)
  · calc
      _ = ∑ i : Fin N, if z.1 (i.val : ZMod N) ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [Fin.is_lt]
      _ = _ := hs (fun x => if z.1 x ≠ 0 then 1 else 0)
  · calc
      _ = ∑ i : Fin N, if z.2 (i.val : ZMod N) ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : ¬ N + i.val < N := by omega
        simp [hi]
      _ = _ := hs (fun x => if z.2 x ≠ 0 then 1 else 0)

theorem M6.Flatten.J_involution : ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Flatten.J N (M6.Flatten.J N v) = v := by
  change ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2 * N)), M6.Flatten.J N (M6.Flatten.J N v) = v
  intro N inst v
  unfold M6.Flatten.J
  rw [M6.Flatten.flatten_left, M6.Physical.J_involution, M6.Flatten.flatten_right]

theorem M6.Flatten.J_weight : ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2*N)), M6.Pinned.weight (M6.Flatten.J N v) = M6.Pinned.weight v := by
  change ∀ (N : ℕ) [NeZero N] (v : M6.Pinned.Vector (2 * N)), M6.Pinned.weight (M6.Flatten.J N v) = M6.Pinned.weight v
  intro N inst v
  unfold M6.Flatten.J
  rw [M6.Flatten.flatten_weight, M6.Physical.J_weight,
    ← M6.Flatten.flatten_weight N (M6.Flatten.unflatten N v),
    M6.Flatten.flatten_right]

theorem M6.Flatten.cycle_orthogonal : ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ↔ ∀ h : M6.Physical.Block N, M6.Character.dot (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))) v = 0 := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ↔ ∀ h : M6.Physical.Block N, M6.Character.dot (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))) v = 0
  intro N inst a b v
  simpa only [← M6.Flatten.flatten_dot, M6.Flatten.flatten_right] using
    (M6.Physical.cycle_orthogonal N a b (M6.Flatten.unflatten N v))
#print axioms M6.Flatten.flatten_add
#print axioms M6.Flatten.flatten_dot
#print axioms M6.Flatten.flatten_left
#print axioms M6.Flatten.flatten_right
#print axioms M6.Flatten.J_involution
#print axioms M6.Flatten.cycle_orthogonal
#print axioms M6.Flatten.flatten_smul
#print axioms M6.Flatten.flatten_weight
#print axioms M6.Flatten.J_weight
