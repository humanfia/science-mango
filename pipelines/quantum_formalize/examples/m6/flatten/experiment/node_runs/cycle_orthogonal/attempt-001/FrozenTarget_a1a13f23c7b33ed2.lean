import M6Flatten

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.Physical.Block N) (v : M6.Pinned.Vector (2*N)), M6.Physical.syndrome N a b (M6.Flatten.unflatten N v) = 0 ↔ ∀ h : M6.Physical.Block N, M6.Character.dot (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N a b h))) v = 0
