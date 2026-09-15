import M6CharacterAccepted
import M6Normalization

theorem M6.Character.constant_transform : ∀ (m : ℕ) (q : M6.Character.Vector m), (q = 0 → M6.Character.localTransform (fun _ _ => (1 : Polynomial ℤ)) q = Polynomial.C ((2 : ℤ)^m)) ∧ (q ≠ 0 → M6.Character.localTransform (fun _ _ => (1 : Polynomial ℤ)) q = 0) := by
  classical
  change ∀ (m : ℕ) (q : M6.Character.Vector m), _
  intro m q
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hz : M6.Character.sign 0 = 1 :=
    ((M6.Character.sign_eq_one 0).1).2 rfl
  have hs (a : ZMod 2) :
      (∑ b : ZMod 2, Polynomial.C (M6.Character.sign (a * b)) * (1 : Polynomial ℤ)) =
        if a = 0 then 2 else 0 := by
    by_cases ha : a = 0
    · subst a
      simp [hu, hz]
    · have hn : M6.Character.sign a = -1 :=
        ((M6.Character.sign_eq_one a).2).2 ha
      simp [hu, hz, hn, ha]
  constructor
  · intro hq
    subst q
    simp only [M6.Character.localTransform, hs]
    simp
  · intro hq
    have hi : ∃ i : Fin m, q i ≠ 0 := by
      by_contra h
      apply hq
      funext i
      simpa using (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hi
    unfold M6.Character.localTransform
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hs, if_neg hi]

theorem M6.FiberSum.sum_by_fibers : ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = M6.FiberSum.fiberSum L w := by
  classical
  change ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = M6.FiberSum.fiberSum L w
  intro α β _ _ L w
  simpa [M6.FiberSum.pullbackSum, M6.FiberSum.fiberSum, M6.FiberSum.fiber,
    Fintype.card_subtype, nsmul_eq_mul] using (Fintype.sum_fiberwise' L w).symm

theorem M6.Character.dual_cardinality : ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)), (M6.Character.subspaceWords D).card * (M6.Character.dualWords D).card = 2^m := by
  classical
  change ∀ (m : ℕ) (D : Submodule (ZMod 2) (M6.Character.Vector m)), _
  intro m D
  have hz : (0 : M6.Character.Vector m) ∈ M6.Character.subspaceWords D := by
    simp [M6.Character.subspaceWords]
  have hd : M6.Character.weightedDual D (fun _ _ => (1 : Polynomial ℤ)) =
      Polynomial.C ((M6.Character.dualWords D).card : ℤ) := by
    simp [M6.Character.weightedDual]
  have ht : M6.Character.weightedTransform D (fun _ _ => (1 : Polynomial ℤ)) =
      Polynomial.C ((2 : ℤ)^m) := by
    unfold M6.Character.weightedTransform
    rw [Finset.sum_eq_single (0 : M6.Character.Vector m)]
    · exact (M6.Character.constant_transform m 0).1 rfl
    · intro q hq hq0
      exact (M6.Character.constant_transform m q).2 hq0
    · intro h
      exact (h hz).elim
  have h := M6.Character.weighted_macwilliams m D (fun _ _ => (1 : Polynomial ℤ))
  rw [hd, ht, ← map_mul] at h
  have hi := Polynomial.C_injective h
  exact_mod_cast hi

theorem M6.FiberSum.uniform_weighted_sum : ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → ∀ (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = Polynomial.C (k : ℤ) * ∑ b, w b := by
  classical
  change ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → ∀ (w : β → Polynomial ℤ), M6.FiberSum.pullbackSum L w = Polynomial.C (k : ℤ) * ∑ b, w b
  intro α β _ _ L k h w
  change ∀ b, (M6.FiberSum.fiber L b).card = k at h
  rw [M6.FiberSum.sum_by_fibers α β L w]
  simp only [M6.FiberSum.fiberSum, h, Finset.mul_sum]

theorem M6.FiberSum.uniform_cardinality : ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → Fintype.card α = k * Fintype.card β := by
  classical
  change ∀ (α β : Type) [Fintype α] [Fintype β] (L : α → β) (k : ℕ), M6.FiberSum.UniformFibers L k → Fintype.card α = k * Fintype.card β
  intro α β _ _ L k h
  change ∀ b, (M6.FiberSum.fiber L b).card = k at h
  have hc : ∀ b, Fintype.card {a : α // L a = b} = k := by
    intro b
    simpa [Fintype.card_subtype, M6.FiberSum.fiber] using h b
  have hs := (Fintype.sum_fiberwise' L (fun _ : β => (1 : ℕ))).symm
  simpa [hc, Nat.mul_comm] using hs
#print axioms M6.Character.constant_transform
#print axioms M6.Character.dual_cardinality
#print axioms M6.FiberSum.sum_by_fibers
#print axioms M6.FiberSum.uniform_weighted_sum
#print axioms M6.FiberSum.uniform_cardinality
