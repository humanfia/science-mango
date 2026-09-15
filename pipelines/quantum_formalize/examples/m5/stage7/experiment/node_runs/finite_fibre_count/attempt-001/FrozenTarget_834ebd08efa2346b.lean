import M5Character

theorem M5.Character.bit_add : ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c := by
  change ∀ a b c : ZMod 2, M5.Character.bitSign a (b + c) = M5.Character.bitSign a b * M5.Character.bitSign a c
  decide

theorem M5.Character.bit_orthogonality : ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0 := by
  change ∀ b : ZMod 2, (∑ a : ZMod 2, M5.Character.bitSign a b) = if b = 0 then 2 else 0
  decide

theorem M5.Character.character_add : ∀ (D : ℕ) (lam z u : M5.Character.BinaryVector D), M5.Character.value lam (z + u) = M5.Character.value lam z * M5.Character.value lam u := by
  change ∀ (D : ℕ) (lam z u : M5.Character.BinaryVector D), M5.Character.value lam (z + u) = M5.Character.value lam z * M5.Character.value lam u
  intro D lam z u
  simp only [M5.Character.value, Pi.add_apply, M5.Character.bit_add, Finset.prod_mul_distrib]

theorem M5.Character.character_orthogonality : ∀ (D : ℕ) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z) = if z = 0 then (2 : ℤ) ^ D else 0 := by
  change ∀ (D : ℕ) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z) = if z = 0 then (2 : ℤ) ^ D else 0
  intro D z
  classical
  change (∑ lam : Fin D → ZMod 2, ∏ i : Fin D, M5.Character.bitSign (lam i) (z i)) = if z = 0 then (2 : ℤ) ^ D else 0
  rw [← Fintype.prod_sum (fun (i : Fin D) (a : ZMod 2) => M5.Character.bitSign a (z i))]
  simp_rw [M5.Character.bit_orthogonality]
  by_cases h : z = 0
  · subst z
    simp
  · rw [if_neg h]
    have hex : ∃ i : Fin D, z i ≠ 0 := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (D n : ℕ) (f : Fin n → M5.Character.BinaryVector D) (z : M5.Character.BinaryVector D), (∑ lam : M5.Character.BinaryVector D, M5.Character.value lam z * ∑ u : Fin n, M5.Character.value lam (f u)) = (2 : ℤ) ^ D * ((Finset.univ.filter (fun u : Fin n => f u = z)).card : ℤ)
