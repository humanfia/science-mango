import M5BirthSearch

theorem M5.BirthSearch.birth_none_iff : ∀ (T lower B : ℕ) (C : ℕ → ℤ), M5.BirthSearch.birth T lower B C = none ↔ ∀ N : ℕ, N ≤ B → lower ≤ N → T ∣ N → C N ≤ 0 := by
  classical
  change ∀ (T lower B : ℕ) (C : ℕ → ℤ), M5.BirthSearch.birth T lower B C = none ↔ ∀ N : ℕ, N ≤ B → lower ≤ N → T ∣ N → C N ≤ 0
  intro T lower B C
  by_cases h : (M5.BirthSearch.candidates T lower B C).Nonempty
  · constructor
    · intro hn
      simp [M5.BirthSearch.birth, h] at hn
    · intro hall
      obtain ⟨N, hN⟩ := h
      have hm : N ≤ B ∧ lower ≤ N ∧ T ∣ N ∧ 0 < C N := by
        simpa [M5.BirthSearch.candidates, Nat.lt_succ_iff, and_assoc, and_left_comm, and_comm] using hN
      exact False.elim ((not_lt_of_ge (hall N hm.1 hm.2.1 hm.2.2.1)) hm.2.2.2)
  · constructor
    · intro _ N hB hl hd
      apply le_of_not_gt
      intro hp
      apply h
      exact ⟨N, by simp [M5.BirthSearch.candidates, Nat.lt_succ_iff, hB, hl, hd, hp]⟩
    · intro _
      simp [M5.BirthSearch.birth, h]

theorem M5.BirthSearch.birth_spec : ∀ (T lower B : ℕ) (C : ℕ → ℤ), (∃ N : ℕ, N ≤ B ∧ lower ≤ N ∧ T ∣ N ∧ 0 < C N) → ∃ b : ℕ, M5.BirthSearch.birth T lower B C = some b ∧ b ≤ B ∧ lower ≤ b ∧ T ∣ b ∧ 0 < C b ∧ ∀ N : ℕ, lower ≤ N → T ∣ N → 0 < C N → b ≤ N := by
  classical
  change ∀ (T lower B : ℕ) (C : ℕ → ℤ), _
  intro T lower B C hex
  have hmem (n : ℕ) : n ∈ M5.BirthSearch.candidates T lower B C ↔
      n ≤ B ∧ lower ≤ n ∧ T ∣ n ∧ 0 < C n := by
    simp [M5.BirthSearch.candidates, Nat.lt_succ_iff, and_assoc, and_left_comm, and_comm]
  have hne : (M5.BirthSearch.candidates T lower B C).Nonempty := by
    obtain ⟨n, hn⟩ := hex
    exact ⟨n, (hmem n).mpr hn⟩
  let b := (M5.BirthSearch.candidates T lower B C).min' hne
  have hb : b ≤ B ∧ lower ≤ b ∧ T ∣ b ∧ 0 < C b :=
    (hmem b).mp (Finset.min'_mem _ hne)
  refine ⟨b, ?_, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, ?_⟩
  · simp [M5.BirthSearch.birth, hne, b]
  · intro N hlow hdiv hpos
    by_cases hNB : N ≤ B
    · exact Finset.min'_le _ N ((hmem N).mpr ⟨hNB, hlow, hdiv, hpos⟩)
    · exact le_trans hb.1 (le_of_lt (Nat.lt_of_not_ge hNB))

theorem M5.BirthSearch.birth_exact : ∀ (T lower B : ℕ) (C : ℕ → ℤ) (Valid : ℕ → Prop), (∀ N : ℕ, Valid N → lower ≤ N ∧ T ∣ N) → (∀ N : ℕ, lower ≤ N → T ∣ N → (0 < C N ↔ Valid N)) → (∃ N : ℕ, N ≤ B ∧ Valid N) → ∃ b : ℕ, M5.BirthSearch.birth T lower B C = some b ∧ Valid b ∧ ∀ N : ℕ, Valid N → b ≤ N := by
  change ∀ (T lower B : ℕ) (C : ℕ → ℤ) (Valid : ℕ → Prop), _
  intro T lower B C Valid hnecessary hexact hwitness
  have hpositive : ∃ N : ℕ, N ≤ B ∧ lower ≤ N ∧ T ∣ N ∧ 0 < C N := by
    obtain ⟨N, hNB, hValid⟩ := hwitness
    obtain ⟨hlower, hdiv⟩ := hnecessary N hValid
    exact ⟨N, hNB, hlower, hdiv, (hexact N hlower hdiv).mpr hValid⟩
  obtain ⟨b, hbirth, hbB, hblower, hbdiv, hbpos, hmin⟩ :=
    M5.BirthSearch.birth_spec T lower B C hpositive
  refine ⟨b, hbirth, (hexact b hblower hbdiv).mp hbpos, ?_⟩
  intro N hValid
  obtain ⟨hlower, hdiv⟩ := hnecessary N hValid
  exact hmin N hlower hdiv ((hexact N hlower hdiv).mpr hValid)
#print axioms M5.BirthSearch.birth_none_iff
#print axioms M5.BirthSearch.birth_spec
#print axioms M5.BirthSearch.birth_exact
