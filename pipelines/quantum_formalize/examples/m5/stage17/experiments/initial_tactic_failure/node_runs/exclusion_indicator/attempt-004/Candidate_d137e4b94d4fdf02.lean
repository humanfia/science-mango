import FrozenTarget_d137e4b94d4fdf02
theorem M5.FiniteExclusion.exclusion_indicator : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (bad : M5.BinaryPolynomial → Bool), M5.FiniteExclusion.exclusionSum S bad = if ∀ p ∈ S, bad p = false then 1 else 0
  intro S bad
  have he : S.filter (fun p => bad p = true) = ∅ ↔ ∀ p ∈ S, bad p = false := by
    constructor
    · intro h p hp
      have hn : bad p ≠ true := by
        intro hb
        have hm : p ∈ S.filter (fun p => bad p = true) :=
          Finset.mem_filter.mpr ⟨hp, hb⟩
        simpa [h] using hm
      cases hb : bad p <;> simp_all
    · intro h
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp
      simp [h p hp]
  calc
    M5.FiniteExclusion.exclusionSum S bad =
        ∑ H ∈ S.powerset.filter (fun H => ∀ p ∈ H, bad p = true), (-1 : ℤ) ^ H.card := by
      change (∑ H ∈ S.powerset, (-1 : ℤ) ^ H.card * (if ∀ p ∈ H, bad p = true then 1 else 0)) = _
      rw [Finset.sum_filter]
      simp only [mul_ite, mul_one, mul_zero]
    _ = ∑ H ∈ (S.filter (fun p => bad p = true)).powerset, (-1 : ℤ) ^ H.card := by
      rw [M5.FiniteExclusion.filtered_powerset]
    _ = if S.filter (fun p => bad p = true) = ∅ then 1 else 0 :=
      M5.FiniteExclusion.alternating_subsets _
    _ = if ∀ p ∈ S, bad p = false then 1 else 0 := by
      rw [he]
