import FrozenTarget_e274143ef4b032c3
theorem M6.Flatten.flatten_weight : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Pinned.weight (M6.Flatten.flatten N z) = M6.Physical.wordWeight N z
  intro N inst z
  let e : Fin N ≃ ZMod N :=
    { toFun := fun i => (i.val : ZMod N)
      invFun := fun x => ⟨x.val, ZMod.val_lt x⟩
      left_inv := by
        intro i
        apply Fin.ext
        exact ZMod.val_natCast_of_lt i.isLt
      right_inv := by
        intro x
        exact ZMod.natCast_zmod_val x }
  have hs (f : ZMod N → ℕ) :
      (∑ i : Fin N, f (i.val : ZMod N)) = ∑ x : ZMod N, f x := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  unfold M6.Pinned.weight M6.Physical.wordWeight M6.Physical.weight M6.Flatten.flatten
  simp only [Finset.card_filter]
  change (∑ i : Fin (2 * N), if (if i.val < N then z.1 (i.val : ZMod N) else z.2 ((i.val - N : ℕ) : ZMod N)) ≠ 0 then 1 else 0) =
    (∑ x : ZMod N, if z.1 x ≠ 0 then 1 else 0) +
    (∑ x : ZMod N, if z.2 x ≠ 0 then 1 else 0)
  rw [show 2 * N = N + N by omega, Fin.sum_univ_add]
  apply congrArg₂ (· + ·)
  · calc
      _ = ∑ i : Fin N, if z.1 (i.val : ZMod N) ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Fin.castAdd, i.isLt]
      _ = _ := hs _
  · calc
      _ = ∑ i : Fin N, if z.2 (i.val : ZMod N) ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have h : ¬ N + i.val < N := by omega
        simp [Fin.natAdd, h]
      _ = _ := hs _
