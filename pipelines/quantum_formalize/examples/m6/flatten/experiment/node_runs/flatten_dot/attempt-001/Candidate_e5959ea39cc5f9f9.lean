import FrozenTarget_e5959ea39cc5f9f9
theorem M6.Flatten.flatten_dot : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (z w : M6.Physical.Word N), M6.Character.dot (M6.Flatten.flatten N z) (M6.Flatten.flatten N w) = M6.Physical.pairing N z w
  intro N inst z w
  classical
  have hsum (f : ZMod N → ZMod 2) :
      (∑ i : Fin N, f (i.val : ZMod N)) = ∑ j : ZMod N, f j := by
    refine Finset.sum_bij (fun i _ => (i.val : ZMod N)) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_univ _
    · intro a ha b hb hab
      apply Fin.ext
      have hv := congrArg (fun x : ZMod N => x.val) hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.is_lt,
        Nat.mod_eq_of_lt b.is_lt] using hv
    · intro j hj
      refine ⟨⟨j.val, ZMod.val_lt j⟩, Finset.mem_univ _, ?_⟩
      simp
    · intro i hi
      rfl
  have hn (i : Fin N) : ¬ N + i.val < N := by omega
  unfold M6.Character.dot M6.Flatten.flatten M6.Physical.pairing M6.Physical.dot
  simp only [two_mul]
  rw [Fin.sum_univ_add]
  simp [Fin.castAdd, Fin.natAdd, hn, hsum]
