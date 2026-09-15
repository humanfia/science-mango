import FrozenTarget_e0dea4e4808f0153
theorem M5.PhysicalRecovery.prefix_extension : QuantumHarnessFrozenTarget := by
  classical
  intro N p q hN hp hq
  have hpq : p.length ≤ q.length := by omega
  have prefix_of_entries : ∀ (a b : List Bool), a.length ≤ b.length →
      (∀ i, i < a.length → a[i]? = b[i]?) → a.IsPrefix b := by
    intro a
    induction a with
    | nil => intro b _ _; exact ⟨b, rfl⟩
    | cons x xs ih =>
      intro b hl he
      cases b with
      | nil => simp at hl
      | cons y ys =>
        have hxy : x = y := by simpa using he 0 (by simp)
        have ht : xs.IsPrefix ys := ih ys (by simpa using hl) (by
          intro i hi
          simpa using he (i + 1) (by simpa using hi))
        rcases ht with ⟨r, hr⟩
        subst y
        exact ⟨r, by simp [← hr]⟩
  have block_forward (offset : ℕ)
      (he : ∀ i, i < p.length → p[i]? = q[i]?) :
      M5.PhysicalRecovery.selected N offset p ⊆ M5.PhysicalRecovery.selected N offset q ∧
      M5.PhysicalRecovery.selected N offset q ⊆
        M5.PhysicalRecovery.selected N offset p ∪ M5.PhysicalRecovery.available N offset p := by
    simp only [M5.PhysicalRecovery.selected, M5.PhysicalRecovery.available,
      Finset.subset_iff, Finset.mem_insert, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range, Finset.mem_union]
    constructor
    · intro a ha
      rcases ha with ha | ⟨i, hi, rfl⟩
      · exact Or.inl ha
      · right
        refine ⟨i, ?_, rfl⟩
        have hei := he (i + offset) (by tauto)
        grind
    · intro a ha
      rcases ha with ha | ⟨i, hi, rfl⟩
      · exact Or.inl (Or.inl ha)
      · by_cases hip : i + offset < p.length
        · left
          right
          refine ⟨i, ?_, rfl⟩
          have hei := he (i + offset) hip
          grind
        · right
          refine ⟨i, ?_, rfl⟩
          grind
  constructor
  · intro h
    have he : ∀ i, i < p.length → p[i]? = q[i]? := by
      rcases h with ⟨r, rfl⟩
      intro i hi
      simp [List.getElem?_append, hi]
    exact ⟨(block_forward 0 he).1, (block_forward 0 he).2,
      (block_forward (N - 1) he).1, (block_forward (N - 1) he).2⟩
  · intro h
    have block_entries (offset : ℕ)
        (h₁ : M5.PhysicalRecovery.selected N offset p ⊆ M5.PhysicalRecovery.selected N offset q)
        (h₂ : M5.PhysicalRecovery.selected N offset q ⊆
          M5.PhysicalRecovery.selected N offset p ∪ M5.PhysicalRecovery.available N offset p)
        (i : ℕ) (hi : i < N - 1) (hip : i + offset < p.length) :
        p[i + offset]? = q[i + offset]? := by
      have hiq : i + offset < q.length := by omega
      have ha : i + 1 ∈ M5.PhysicalRecovery.selected N offset p →
          i + 1 ∈ M5.PhysicalRecovery.selected N offset q := fun hx => h₁ hx
      have hb : i + 1 ∈ M5.PhysicalRecovery.selected N offset q →
          i + 1 ∈ M5.PhysicalRecovery.selected N offset p ∪
            M5.PhysicalRecovery.available N offset p := fun hx => h₂ hx
      simp only [M5.PhysicalRecovery.selected, M5.PhysicalRecovery.available,
        Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
        Finset.mem_range, Finset.mem_union] at ha hb
      have hpi : p[i + offset]? = some p[i + offset] := by simp [hip]
      have hqi : q[i + offset]? = some q[i + offset] := by simp [hiq]
      cases ep : p[i + offset] <;> cases eq : q[i + offset] <;> grind
    apply prefix_of_entries p q hpq
    intro i hi
    by_cases hia : i < N - 1
    · simpa using block_entries 0 h.1 h.2.1 i hia (by simpa using hi)
    · have hcount : p.length ≤ 2 * (N - 1) := by
        simpa [M5.PhysicalRecovery.decisionCount] using hp
      have hib : i - (N - 1) < N - 1 := by omega
      have heq : i - (N - 1) + (N - 1) = i := by omega
      simpa only [heq] using
        block_entries (N - 1) h.2.2.1 h.2.2.2 (i - (N - 1)) hib (by omega)
