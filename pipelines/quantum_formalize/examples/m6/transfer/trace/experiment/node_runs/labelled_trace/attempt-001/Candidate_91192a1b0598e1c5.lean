import FrozenTarget_91192a1b0598e1c5
theorem M6.Transfer.labelled_trace : QuantumHarnessFrozenTarget := by
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
