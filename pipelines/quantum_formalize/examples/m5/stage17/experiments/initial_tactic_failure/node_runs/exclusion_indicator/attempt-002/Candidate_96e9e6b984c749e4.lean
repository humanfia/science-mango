import FrozenTarget_96e9e6b984c749e4
theorem M5.FiniteExclusion.exclusion_indicator : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), M5.FiniteExclusion.exclusionSum S bad = if ∀ p ∈ S, bad p = false then 1 else 0
  intro S bad
  change (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card * (if ∀ p ∈ H, bad p = true then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [M5.FiniteExclusion.filtered_powerset, M5.FiniteExclusion.alternating_subsets]
  have h : S.filter (fun p => bad p = true) = ∅ ↔ ∀ p ∈ S, bad p = false := by
    constructor
    · intro he p hp
      cases hb : bad p with
      | false => rfl
      | true =>
        have hm : p ∈ S.filter (fun p => bad p = true) := Finset.mem_filter.mpr ⟨hp, hb⟩
        rw [he] at hm
        exact False.elim (Finset.not_mem_empty p hm)
    · intro hall
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro p hp
      obtain ⟨hpS, htrue⟩ := Finset.mem_filter.mp hp
      have hfalse := hall p hpS
      rw [hfalse] at htrue
      cases htrue
  simp only [h]
