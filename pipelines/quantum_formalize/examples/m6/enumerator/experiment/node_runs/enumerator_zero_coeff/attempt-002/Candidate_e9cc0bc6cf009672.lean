import FrozenTarget_e9cc0bc6cf009672
theorem M6.Pinned.enumerator_zero_coeff : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), (0 : M6.Pinned.Vector m) ∉ L → (M6.Pinned.enumerator L P).coeff 0 = 0
  intro m L P hzero
  classical
  rw [M6.Pinned.enumerator_coeff m L P 0]
  obtain ⟨hnonneg, hpos⟩ := M6.Pinned.count_nonnegative_positive m L P 0
  have hnotpos : ¬ 0 < M6.Pinned.count L P 0 := by
    intro h
    obtain ⟨v, hv, _, hw⟩ := hpos.mp h
    have hvzero : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      unfold M6.Pinned.weight at hw
      have he := Finset.card_eq_zero.mp hw
      have hm : i ∈ Finset.univ.filter (fun j => v j ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [he] at hm
      exact Finset.not_mem_empty i hm
    exact hzero (hvzero ▸ hv)
  omega
