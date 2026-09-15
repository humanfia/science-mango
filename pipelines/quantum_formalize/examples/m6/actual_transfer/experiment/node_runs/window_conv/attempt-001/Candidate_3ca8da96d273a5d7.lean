import FrozenTarget_3ca8da96d273a5d7
theorem M6.ActualTransfer.window_conv : QuantumHarnessFrozenTarget := by
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
