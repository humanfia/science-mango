import FrozenTarget_fc4de09a5e0f3cc2
theorem M6.ActualTransfer.product_halves : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (w : Fin (2*N) → ZMod 2 → Polynomial ℤ), (∏ q, w q (M6.Flatten.flatten N z q)) = ∏ i : ZMod N, w (M6.ActualTransfer.leftIndex N i) (z.1 i) * w (M6.ActualTransfer.rightIndex N i) (z.2 i)
  intro N inst z w
  classical
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    let f : ZMod (n+1) ⊕ ZMod (n+1) → Fin (2*(n+1)) :=
      Sum.elim (M6.ActualTransfer.leftIndex (n+1)) (M6.ActualTransfer.rightIndex (n+1))
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        cases a with
        | inl i =>
          cases b with
          | inl j =>
            have hv := congrArg Fin.val h
            apply congrArg Sum.inl
            apply Fin.ext
            exact hv
          | inr j =>
            have hv := congrArg Fin.val h
            have hi := ZMod.val_lt i
            dsimp [f, M6.ActualTransfer.leftIndex, M6.ActualTransfer.rightIndex] at hv
            omega
        | inr i =>
          cases b with
          | inl j =>
            have hv := congrArg Fin.val h
            have hj := ZMod.val_lt j
            dsimp [f, M6.ActualTransfer.leftIndex, M6.ActualTransfer.rightIndex] at hv
            omega
          | inr j =>
            have hv := congrArg Fin.val h
            apply congrArg Sum.inr
            apply Fin.ext
            dsimp [f, M6.ActualTransfer.rightIndex, ZMod.val] at hv
            omega
      · intro q
        by_cases hq : q.val < n+1
        · refine ⟨Sum.inl (show ZMod (n+1) from (⟨q.val, hq⟩ : Fin (n+1))), ?_⟩
          apply Fin.ext
          rfl
        · have hb : q.val - (n+1) < n+1 := by omega
          refine ⟨Sum.inr (show ZMod (n+1) from (⟨q.val - (n+1), hb⟩ : Fin (n+1))), ?_⟩
          apply Fin.ext
          dsimp [f, M6.ActualTransfer.rightIndex, ZMod.val]
          omega
    let e := Equiv.ofBijective f hf
    have hp := Fintype.prod_equiv e
      (fun s => w (f s) (M6.Flatten.flatten (n+1) z (f s)))
      (fun q => w q (M6.Flatten.flatten (n+1) z q))
      (fun s => rfl)
    rw [← hp, Fintype.prod_sum_type]
    change (∏ i : ZMod (n+1), w (M6.ActualTransfer.leftIndex (n+1) i) (M6.Flatten.flatten (n+1) z (M6.ActualTransfer.leftIndex (n+1) i))) * (∏ i : ZMod (n+1), w (M6.ActualTransfer.rightIndex (n+1) i) (M6.Flatten.flatten (n+1) z (M6.ActualTransfer.rightIndex (n+1) i))) = _
    simp only [M6.ActualTransfer.left_coordinate, M6.ActualTransfer.right_coordinate, Finset.prod_mul_distrib]
