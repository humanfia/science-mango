import FrozenTarget_5e51b76f232d87cd
theorem M6.Character.constant_transform : QuantumHarnessFrozenTarget := by
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
