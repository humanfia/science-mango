import FrozenTarget_9b92ddfa9a35954f
theorem M5.PhysicalRecovery.prefix_extension : QuantumHarnessFrozenTarget := by
  classical
  intro N p q hN hp hq
  have hlen : p.length ≤ q.length := by omega
  have prefix_iff : p.IsPrefix q ↔ ∀ (i : ℕ) (hi : i < p.length), p[i] = q[i]'(by omega) := by
    constructor
    · rintro ⟨r, rfl⟩ i hi
      simp [hi]
    · intro h
      have he : p = q.take p.length := by
        apply List.ext_getElem
        · simp [Nat.min_eq_left hlen]
        · intro i hi hj
          simpa using h i hi
      refine ⟨q.drop p.length, ?_⟩
      rw [he, List.take_append_drop]
  rw [prefix_iff]
  constructor
  · intro h
    have he : ∀ i, i < p.length → p[i]? = q[i]? := by
      intro i hi
      have hqi : i < q.length := by omega
      simp [List.getElem?_eq_getElem, hi, hqi, h i hi]
    simp only [M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selectedB,
      M5.PhysicalRecovery.availableA, M5.PhysicalRecovery.availableB,
      M5.PhysicalRecovery.selected, M5.PhysicalRecovery.available,
      M5.OrderCount.positivePositions, Finset.subset_iff,
      Finset.mem_union, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_range] at *
    repeat first | apply And.intro | intro x hx
    all_goals
      simp_all [List.getD]
      grind
  · intro h i hi
    have hqi : i < q.length := by omega
    have hib : i < 2 * (N - 1) := by
      simp only [M5.PhysicalRecovery.decisionCount] at hp
      omega
    by_cases hblock : i < N - 1
    · have h1 := Finset.subset_iff.mp h.1 (i + 1)
      have h2 := Finset.subset_iff.mp h.2.1 (i + 1)
      simp [M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.availableA,
        M5.PhysicalRecovery.selected, M5.PhysicalRecovery.available,
        M5.OrderCount.positivePositions, List.getD, hi, hqi,
        List.getElem?_eq_getElem] at h1 h2
      cases hpi : p[i] <;> cases hqj : q[i] <;> simp_all <;> grind
    · let s := i - (N - 1) + 1
      have hs0 : s ≠ 0 := by omega
      have hsN : s < N := by omega
      have hs1 : N - 1 + (s - 1) = i := by omega
      have hs2 : N - 1 + s - 1 = i := by omega
      have h1 := Finset.subset_iff.mp h.2.2.1 s
      have h2 := Finset.subset_iff.mp h.2.2.2 s
      simp [M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.availableB,
        M5.PhysicalRecovery.selected, M5.PhysicalRecovery.available,
        M5.OrderCount.positivePositions, hs0, hsN, hs1, hs2,
        List.getD, hi, hqi, List.getElem?_eq_getElem] at h1 h2
      cases hpi : p[i] <;> cases hqj : q[i] <;> simp_all <;> grind
