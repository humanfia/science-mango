import FrozenTarget_ca2a4f6ce614d181
theorem M6.ActualTransfer.product_halves : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (w : Fin (2*N) → ZMod 2 → Polynomial ℤ), (∏ q, w q (M6.Flatten.flatten N z q)) = ∏ i : ZMod N, w (M6.ActualTransfer.leftIndex N i) (z.1 i) * w (M6.ActualTransfer.rightIndex N i) (z.2 i)
  intro N inst z w
  classical
  let j : Sum (ZMod N) (ZMod N) → Fin (2*N) := Sum.elim (M6.ActualTransfer.leftIndex N) (M6.ActualTransfer.rightIndex N)
  have hj : Function.Bijective j := by
    constructor
    · intro a b h
      cases a with
      | inl i =>
        cases b with
        | inl k =>
          have hv := congrArg Fin.val h
          change i.val = k.val at hv
          exact congrArg Sum.inl (ZMod.val_injective hv)
        | inr k =>
          have hv := congrArg Fin.val h
          change i.val = N + k.val at hv
          have hi := ZMod.val_lt i
          omega
      | inr i =>
        cases b with
        | inl k =>
          have hv := congrArg Fin.val h
          change N + i.val = k.val at hv
          have hk := ZMod.val_lt k
          omega
        | inr k =>
          have hv := congrArg Fin.val h
          change N + i.val = N + k.val at hv
          exact congrArg Sum.inr (ZMod.val_injective (by omega))
    · intro q
      by_cases hq : q.val < N
      · refine ⟨Sum.inl (q.val : ZMod N), ?_⟩
        apply Fin.ext
        change (q.val : ZMod N).val = q.val
        simp [ZMod.val_natCast, Nat.mod_eq_of_lt hq]
      · have hr : q.val - N < N := by omega
        refine ⟨Sum.inr ((q.val - N : ℕ) : ZMod N), ?_⟩
        apply Fin.ext
        change N + ((q.val - N : ℕ) : ZMod N).val = q.val
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr]
        omega
  let e : Sum (ZMod N) (ZMod N) ≃ Fin (2*N) := Equiv.ofBijective j hj
  have hp := Fintype.prod_equiv e
    (fun s => w (j s) (M6.Flatten.flatten N z (j s)))
    (fun q => w q (M6.Flatten.flatten N z q))
    (fun s => rfl)
  rw [← hp]
  simp only [Fintype.prod_sum_type, j, Sum.elim_inl, Sum.elim_inr,
    M6.ActualTransfer.left_coordinate, M6.ActualTransfer.right_coordinate,
    Finset.prod_mul_distrib]
