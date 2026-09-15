import M5PhysicalRecovery

theorem M5.PhysicalRecovery.decode_encode : ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → A ⊆ Finset.range N → B ⊆ Finset.range N → 0 ∈ A → 0 ∈ B → (M5.PhysicalRecovery.selectedA N (M5.PhysicalRecovery.encode N A B) = A ∧ M5.PhysicalRecovery.selectedB N (M5.PhysicalRecovery.encode N A B) = B) := by
  classical
  intro N A B hN hA hB hA0 hB0
  have decode_block (offset : ℕ) (p : List Bool) (S : Finset ℕ)
      (hS : S ⊆ Finset.range N) (hS0 : 0 ∈ S)
      (hp : ∀ i < N - 1,
        (offset + i < p.length ∧ p[offset + i]? = some true) ↔ i + 1 ∈ S) :
      M5.PhysicalRecovery.selected N offset p = S := by
    ext s
    simp only [M5.PhysicalRecovery.selected, Finset.mem_insert,
      Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hs
      rcases hs with hs | ⟨i, ⟨hi, hpi⟩, his⟩
      · subst s
        exact hS0
      · have hm := (hp i hi).mp hpi
        simpa only [his] using hm
    · intro hs
      by_cases hs0 : s = 0
      · exact Or.inl hs0
      · right
        have hsN : s < N := Finset.mem_range.mp (hS hs)
        have hi : s - 1 < N - 1 := by omega
        have he : s - 1 + 1 = s := by omega
        refine ⟨s - 1, ⟨hi, ?_⟩, he⟩
        apply (hp (s - 1) hi).mpr
        simpa only [he] using hs
  constructor
  · change M5.PhysicalRecovery.selected N 0 (M5.PhysicalRecovery.encode N A B) = A
    apply decode_block 0 (M5.PhysicalRecovery.encode N A B) A hA hA0
    intro i hi
    have hit : i < 2 * (N - 1) := by omega
    simp [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.decisionCount, hi, hit]
  · change M5.PhysicalRecovery.selected N (N - 1) (M5.PhysicalRecovery.encode N A B) = B
    apply decode_block (N - 1) (M5.PhysicalRecovery.encode N A B) B hB hB0
    intro i hi
    have hit : N - 1 + i < 2 * (N - 1) := by omega
    have hnot : ¬ N - 1 + i < N - 1 := by omega
    simp [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.decisionCount, hit, hnot]

theorem M5.PhysicalRecovery.encode_decode : ∀ (N : ℕ) (q : List Bool), 0 < N → q.length = M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) = q := by
  change ∀ (N : ℕ) (q : List Bool), 0 < N → q.length = M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N q) (M5.PhysicalRecovery.selectedB N q) = q
  intro N q hN hq
  have hmem (offset j : ℕ) (hj : j < N - 1) (hjq : offset + j < q.length) :
      (j + 1 ∈ M5.PhysicalRecovery.selected N offset q) ↔ q[offset + j] = true := by
    cases hb : q[offset + j] <;>
      simp [M5.PhysicalRecovery.selected, Finset.mem_image, List.getD,
        List.getElem?_eq_getElem, Nat.add_comm, hj, hjq, hb]
  apply List.ext_getElem
  · simpa [M5.PhysicalRecovery.encode] using hq.symm
  · intro i hi hiq
    have hic : i < M5.PhysicalRecovery.decisionCount N := by omega
    have hib : i < 2 * (N - 1) := by
      simpa [M5.PhysicalRecovery.decisionCount] using hic
    by_cases hfirst : i < N - 1
    · have hm := hmem 0 i hfirst (by omega)
      simp only [Nat.zero_add] at hm
      cases hb : q[i] <;>
        simp [hb] at hm <;>
        simp [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.selectedA,
          hfirst, hm, hb]
    · have hj : i - (N - 1) < N - 1 := by omega
      have hoff : N - 1 + (i - (N - 1)) = i := by omega
      have hm := hmem (N - 1) (i - (N - 1)) hj (by omega)
      simp only [hoff] at hm
      cases hb : q[i] <;>
        simp [hb] at hm <;>
        simp [M5.PhysicalRecovery.encode, M5.PhysicalRecovery.selectedB,
          hfirst, hm, hb]

theorem M5.PhysicalRecovery.prefix_extension : ∀ (N : ℕ) (p q : List Bool), 0 < N → p.length ≤ M5.PhysicalRecovery.decisionCount N → q.length = M5.PhysicalRecovery.decisionCount N → (p.IsPrefix q ↔ M5.PhysicalRecovery.selectedA N p ⊆ M5.PhysicalRecovery.selectedA N q ∧ M5.PhysicalRecovery.selectedA N q ⊆ M5.PhysicalRecovery.selectedA N p ∪ M5.PhysicalRecovery.availableA N p ∧ M5.PhysicalRecovery.selectedB N p ⊆ M5.PhysicalRecovery.selectedB N q ∧ M5.PhysicalRecovery.selectedB N q ⊆ M5.PhysicalRecovery.selectedB N p ∪ M5.PhysicalRecovery.availableB N p) := by
  intro N p q hN hp hq
  have hpq : p.length ≤ q.length := by omega
  have prefix_of_entries : ∀ (a b : List Bool), a.length ≤ b.length →
      (∀ i, i < a.length → a[i]? = b[i]?) → a.IsPrefix b := by
    intro a
    induction a with
    | nil => intro b hl he; exact ⟨b, rfl⟩
    | cons x a ih =>
      intro b hl he
      cases b with
      | nil => simp at hl
      | cons y b =>
        have hxy : x = y := by simpa using he 0 (by simp)
        subst y
        have hab : a.IsPrefix b := ih b (by simpa using hl) (by
          intro i hi
          simpa using he (i + 1) (by simpa using hi))
        obtain ⟨r, hr⟩ := hab
        exact ⟨r, by simp [hr]⟩
  have ms : ∀ (offset i : ℕ) (r : List Bool),
      i + 1 ∈ M5.PhysicalRecovery.selected N offset r ↔
        i < N - 1 ∧ offset + i < r.length ∧ r[offset + i]? = some true := by
    intro offset i r
    simp [M5.PhysicalRecovery.selected]
  have ma : ∀ (offset i : ℕ) (r : List Bool),
      i + 1 ∈ M5.PhysicalRecovery.available N offset r ↔
        i < N - 1 ∧ r.length ≤ offset + i := by
    intro offset i r
    simp [M5.PhysicalRecovery.available]
  have block_forward : ∀ offset,
      (∀ i, i < p.length → p[i]? = q[i]?) →
      M5.PhysicalRecovery.selected N offset p ⊆ M5.PhysicalRecovery.selected N offset q ∧
      M5.PhysicalRecovery.selected N offset q ⊆
        M5.PhysicalRecovery.selected N offset p ∪ M5.PhysicalRecovery.available N offset p := by
    intro offset he
    constructor
    · intro x hx
      simp only [M5.PhysicalRecovery.selected, Finset.mem_insert,
        Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx ⊢
      rcases hx with hx | ⟨i, ⟨hi, hip, hit⟩, hix⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, ⟨hi, lt_of_lt_of_le hip hpq, (he _ hip).symm.trans hit⟩, hix⟩
    · intro x hx
      simp only [M5.PhysicalRecovery.selected, Finset.mem_insert,
        Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx
      rcases hx with hx | ⟨i, ⟨hi, hiq, hit⟩, hix⟩
      · subst x
        apply Finset.mem_union_left
        simp [M5.PhysicalRecovery.selected]
      · subst x
        by_cases hip : offset + i < p.length
        · apply Finset.mem_union_left
          exact (ms offset i p).2 ⟨hi, hip, (he _ hip).trans hit⟩
        · apply Finset.mem_union_right
          exact (ma offset i p).2 ⟨hi, by omega⟩
  constructor
  · intro h
    have he : ∀ i, i < p.length → p[i]? = q[i]? := by
      obtain ⟨r, rfl⟩ := h
      intro i hi
      simp [List.getElem?_append, hi]
    have ha := block_forward 0 he
    have hb := block_forward (N - 1) he
    exact ⟨ha.1, ha.2, hb.1, hb.2⟩
  · intro h
    have block_entries : ∀ offset,
        M5.PhysicalRecovery.selected N offset p ⊆ M5.PhysicalRecovery.selected N offset q →
        M5.PhysicalRecovery.selected N offset q ⊆
          M5.PhysicalRecovery.selected N offset p ∪ M5.PhysicalRecovery.available N offset p →
        ∀ i, i < N - 1 → offset + i < p.length →
          p[offset + i]? = q[offset + i]? := by
      intro offset h₁ h₂ i hi hip
      have hiq : offset + i < q.length := lt_of_lt_of_le hip hpq
      have ht : p[offset + i]? = some true ↔ q[offset + i]? = some true := by
        constructor
        · intro ht
          exact ((ms offset i q).1 (h₁ ((ms offset i p).2 ⟨hi, hip, ht⟩))).2.2
        · intro ht
          have hm := h₂ ((ms offset i q).2 ⟨hi, hiq, ht⟩)
          rcases Finset.mem_union.mp hm with hm | hm
          · exact ((ms offset i p).1 hm).2.2
          · have := ((ma offset i p).1 hm).2
            omega
      have hpi : p[offset + i]? = some p[offset + i] := getElem?_pos p (offset + i) hip
      have hqi : q[offset + i]? = some q[offset + i] := getElem?_pos q (offset + i) hiq
      rw [hpi, hqi] at ht ⊢
      cases ep : p[offset + i] <;> cases eq : q[offset + i] <;> simp_all
    apply prefix_of_entries p q hpq
    intro i hi
    by_cases hai : i < N - 1
    · simpa using block_entries 0 h.1 h.2.1 i hai (by simpa using hi)
    · have hbi : i - (N - 1) < N - 1 := by
        unfold M5.PhysicalRecovery.decisionCount at hp
        omega
      have he : (N - 1) + (i - (N - 1)) = i := by omega
      simpa only [he] using block_entries (N - 1) h.2.2.1 h.2.2.2
        (i - (N - 1)) hbi (by omega)

theorem M5.PhysicalRecovery.state_domains : ∀ (N : ℕ) (p : List Bool), 0 < N → p.length ≤ M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.StateOK N p := by
  change ∀ (N : ℕ) (p : List Bool), 0 < N → p.length ≤ M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.StateOK N p
  intro N p hN hp
  simp only [M5.PhysicalRecovery.StateOK,
    M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selectedB,
    M5.PhysicalRecovery.availableA, M5.PhysicalRecovery.availableB,
    M5.PhysicalRecovery.selected, M5.PhysicalRecovery.available,
    Finset.subset_iff, Finset.disjoint_left, Finset.mem_insert,
    Finset.mem_image, Finset.mem_filter, Finset.mem_range,
    Finset.mem_singleton]
  aesop (config := { terminal := false }) <;> omega
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length ≤ M5.PhysicalRecovery.decisionCount N → (M5.PhysicalRecovery.selectedA N p).card ≤ w → (M5.PhysicalRecovery.selectedB N p).card ≤ w → M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p = (M5.PhysicalRecovery.completionSet N w F p).card
