import M6ActualTransferReady

theorem M6.ActualTransfer.left_coordinate : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.leftIndex N i) = z.1 i := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.leftIndex N i) = z.1 i
  intro N inst z i
  simp [M6.Flatten.flatten, M6.ActualTransfer.leftIndex, ZMod.val_lt i]

theorem M6.ActualTransfer.right_coordinate : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.rightIndex N i) = z.2 i := by
  change ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (i : ZMod N), M6.Flatten.flatten N z (M6.ActualTransfer.rightIndex N i) = z.2 i
  intro N inst z i
  have h₁ : ¬ N + i.val < N := by omega
  have h₂ : ¬ i.val + N < N := by omega
  simp [M6.Flatten.flatten, M6.ActualTransfer.rightIndex, h₁, h₂]

theorem M6.ActualTransfer.window_conv : ∀ (R N : ℕ) [NeZero N] (a : M6.ActualTransfer.BP), a.natDegree ≤ R → R < N → ∀ (h : M6.Transfer.Input N) (i : ZMod N), M6.Transfer.cyclicOutput (M6.ActualTransfer.window R a) h i = M6.Physical.conv N (M6.Coordinates.coefficients N a) h i := by
  classical
  intro R N inst a ha hRN h i
  change (∑ j : Fin (R + 1), a.coeff j.val * h (i - (j.val : ZMod N))) =
    ∑ j : ZMod N, a.coeff j.val * h (i - j)
  have hv (j : Fin (R + 1)) : ((j.val : ZMod N)).val = j.val := by
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt (show j.val < N by omega)]
  calc
    (∑ j : Fin (R + 1), a.coeff j.val * h (i - (j.val : ZMod N))) =
        ∑ j ∈ Finset.univ.filter (fun j : ZMod N => j.val < R + 1),
          a.coeff j.val * h (i - j) := by
      refine Finset.sum_bij (fun j _ => (j.val : ZMod N)) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv]
        exact j.isLt
      · intro j hj k hk hjk
        apply Fin.ext
        have he := congrArg (fun x : ZMod N => x.val) hjk
        simpa only [hv] using he
      · intro j hj
        have hjlt : j.val < R + 1 := (Finset.mem_filter.mp hj).2
        refine ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, ?_⟩
        simp
      · intro j hj
        rw [hv]
    _ = ∑ j : ZMod N, a.coeff j.val * h (i - j) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hjout
      have hjlarge : ¬j.val < R + 1 := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hjout
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show a.natDegree < j.val by omega), zero_mul]

theorem M6.ActualTransfer.product_halves : ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N) (w : Fin (2*N) → ZMod 2 → Polynomial ℤ), (∏ q, w q (M6.Flatten.flatten N z q)) = ∏ i : ZMod N, w (M6.ActualTransfer.leftIndex N i) (z.1 i) * w (M6.ActualTransfer.rightIndex N i) (z.2 i) := by
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

theorem M6.ActualTransfer.boundary_input_product : ∀ (R N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), a.natDegree ≤ R → b.natDegree ≤ R → R < N → ∀ (P : M6.Pinned.Pins (2*N)) (h : M6.Transfer.Input N), (∏ i : ZMod N, M6.ActualTransfer.boundaryWeight R N a b P i.val (M6.Transfer.memoryAt h i) (h i)) = M6.Character.pinnedMonomial P (M6.Flatten.flatten N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) := by
  classical
  intro R N inst a b ha hb hRN P h
  rw [← M6.Character.pinned_product, M6.ActualTransfer.product_halves]
  apply Finset.prod_congr rfl
  intro i hi
  simp [M6.ActualTransfer.boundaryWeight, M6.Physical.boundary,
    M6.Transfer.output_convolution,
    M6.ActualTransfer.window_conv R N a ha hRN,
    M6.ActualTransfer.window_conv R N b hb hRN]

theorem M6.ActualTransfer.character_input_product : ∀ (R N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), a.natDegree ≤ R → b.natDegree ≤ R → R < N → ∀ (P : M6.Pinned.Pins (2*N)) (h : M6.Transfer.Input N), (∏ i : ZMod N, M6.ActualTransfer.characterWeight R N a b P i.val (M6.Transfer.memoryAt h i) (h i)) = ∏ q : Fin (2*N), M6.Character.pinnedCharacterFactor P q (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) q) := by
  classical
  intro R N inst a b ha hb hRN P h
  rw [M6.ActualTransfer.product_halves]
  refine Finset.prod_bij (fun i _ => -i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj hij
    exact neg_injective hij
  · intro j hj
    exact ⟨-j, Finset.mem_univ _, neg_neg j⟩
  · intro i hi
    simp [M6.ActualTransfer.characterWeight,
      M6.Transfer.output_convolution,
      M6.ActualTransfer.window_conv R N a ha hRN,
      M6.ActualTransfer.window_conv R N b hb hRN,
      M6.Physical.J, M6.Physical.boundary, M6.Physical.rev, mul_comm]
#print axioms M6.ActualTransfer.left_coordinate
#print axioms M6.ActualTransfer.right_coordinate
#print axioms M6.ActualTransfer.product_halves
#print axioms M6.ActualTransfer.window_conv
#print axioms M6.ActualTransfer.boundary_input_product
#print axioms M6.ActualTransfer.character_input_product
