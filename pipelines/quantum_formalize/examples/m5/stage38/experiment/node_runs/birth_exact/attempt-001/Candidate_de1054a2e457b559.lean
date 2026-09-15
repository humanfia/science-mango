import FrozenTarget_de1054a2e457b559
theorem M5.BirthSearch.birth_exact : QuantumHarnessFrozenTarget := by
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
