import FrozenTarget_fc41fab2689d9a5e
theorem M6.Character.pinned_product : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Character.Vector m), (∏ i, M6.Character.boundaryFactor P i (v i)) = M6.Character.pinnedMonomial P v
  intro m P v
  classical
  by_cases h : M6.Pinned.agrees P v
  · rw [M6.Character.pinnedMonomial, if_pos h, M6.Character.weight_as_sum]
    rw [Finset.pow_sum]
    apply Finset.prod_congr rfl
    intro i hi
    unfold M6.Pinned.agrees at h
    have hv := h i
    cases hp : P i <;>
      generalize hs : v i = s at hv ⊢ <;>
      fin_cases s <;>
      simp_all [M6.Character.boundaryFactor, ZMod.val_zero, ZMod.val_one_eq_one_mod]
  · rw [M6.Character.pinnedMonomial, if_neg h]
    by_contra hn
    apply h
    unfold M6.Pinned.agrees
    intro i
    have hi : M6.Character.boundaryFactor P i (v i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
    cases hp : P i <;>
      simp_all [M6.Character.boundaryFactor]
