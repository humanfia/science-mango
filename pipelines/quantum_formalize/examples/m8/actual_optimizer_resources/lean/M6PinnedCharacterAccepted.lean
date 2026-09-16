import M6CharacterAccepted
import M6PinnedCharacter

theorem M6.Character.free_character_factor : ∀ (m : ℕ) (i : Fin m) (s : ZMod 2), M6.Character.pinnedCharacterFactor (M6.Pinned.free m) i s = 1 + Polynomial.C (M6.Character.sign s) * Polynomial.X := by
  change ∀ (m : ℕ) (i : Fin m) (s : ZMod 2), M6.Character.pinnedCharacterFactor (M6.Pinned.free m) i s = 1 + Polynomial.C (M6.Character.sign s) * Polynomial.X
  intro m i s
  classical
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hv : (1 : ZMod 2).val = 1 := rfl
  simp [M6.Character.pinnedCharacterFactor, M6.Character.boundaryFactor,
    M6.Pinned.free, h, M6.Character.sign, hv]

theorem M6.Character.weight_as_sum : ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val := by
  change ∀ (m : ℕ) (v : M6.Character.Vector m), M6.Pinned.weight v = ∑ i, (v i).val
  intro m v
  classical
  unfold M6.Pinned.weight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  generalize hx : v i = x
  have hx01 : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx01 with rfl | rfl <;> norm_num [ZMod.val_zero, ZMod.val_one_eq_one_mod]

theorem M6.Character.pinned_product : ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Character.Vector m), (∏ i, M6.Character.boundaryFactor P i (v i)) = M6.Character.pinnedMonomial P v := by
  change ∀ (m : ℕ) (P : M6.Pinned.Pins m) (v : M6.Character.Vector m), (∏ i, M6.Character.boundaryFactor P i (v i)) = M6.Character.pinnedMonomial P v
  intro m P v
  classical
  by_cases h : M6.Pinned.agrees P v
  · rw [M6.Character.pinnedMonomial, if_pos h]
    have hf : ∀ i, M6.Character.boundaryFactor P i (v i) = (Polynomial.X : Polynomial ℤ) ^ (v i).val := by
      intro i
      unfold M6.Pinned.agrees at h
      have hi := h i
      cases hp : P i <;> simp_all [M6.Character.boundaryFactor]
    simp_rw [hf]
    rw [M6.Character.weight_as_sum]
    have hp : ∀ s : Finset (Fin m), (∏ i ∈ s, (Polynomial.X : Polynomial ℤ) ^ (v i).val) = Polynomial.X ^ (∑ i ∈ s, (v i).val) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => simp [hi, ih, pow_add]
    exact hp Finset.univ
  · rw [M6.Character.pinnedMonomial, if_neg h]
    by_contra hn
    apply h
    unfold M6.Pinned.agrees
    intro i
    have hi := Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i)
    cases hp : P i <;> simp [M6.Character.boundaryFactor, hp] at hi ⊢ <;> aesop

theorem M6.Character.pinned_macwilliams : ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (P : M6.Pinned.Pins m), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Pinned.enumerator (M6.Character.dualWords D) P = M6.Character.pinnedTransform D P := by
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)) (P : M6.Pinned.Pins m), Polynomial.C ((M6.Character.subspaceWords D).card : ℤ) * M6.Pinned.enumerator (M6.Character.dualWords D) P = M6.Character.pinnedTransform D P
  intro m D P
  classical
  simpa [M6.Character.weightedDual, M6.Character.weightedTransform,
    M6.Character.localTransform, M6.Character.pinnedTransform,
    M6.Character.pinnedCharacterFactor, M6.Character.pinned_product,
    M6.Character.pinnedMonomial, M6.Pinned.enumerator, Finset.sum_filter]
    using M6.Character.weighted_macwilliams m D (M6.Character.boundaryFactor P)
#print axioms M6.Character.free_character_factor
#print axioms M6.Character.weight_as_sum
#print axioms M6.Character.pinned_product
#print axioms M6.Character.pinned_macwilliams
