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

theorem M5.PhysicalRecovery.valid_words_length : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (q : List Bool), q ∈ M5.PhysicalRecovery.validWords N w F → q.length = M5.PhysicalRecovery.decisionCount N := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (q : List Bool), q ∈ M5.PhysicalRecovery.validWords N w F → q.length = M5.PhysicalRecovery.decisionCount N
  intro N w F q h
  classical
  simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter, M5.PhysicalRecovery.wordValid] at h
  tauto

theorem M5.PhysicalRecovery.initial_oracle : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.PhysicalRecovery.oracle N w F [] = M5.OrderCount.C N w F := by
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → M5.PhysicalRecovery.oracle N w F [] = M5.OrderCount.C N w F
  intro N w F hN hw hF hFd
  classical
  have hs (offset : ℕ) : M5.PhysicalRecovery.selected N offset [] = {0} := by
    simp [M5.PhysicalRecovery.selected]
  have ha (offset : ℕ) : M5.PhysicalRecovery.available N offset [] = M5.OrderCount.positivePositions N := by
    ext i
    simp [M5.PhysicalRecovery.available, M5.OrderCount.positivePositions]
    constructor
    · aesop (config := { terminal := false }) <;> omega
    · intro hi
      first
      | omega
      | exact ⟨i - 1, by omega, by omega⟩
  have hprefix : M5.ConditionalCount.PrefixOK N w {0} {0}
      (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) := by
    simp [M5.ConditionalCount.PrefixOK, M5.OrderCount.positivePositions,
      Finset.subset_iff, Finset.disjoint_left]
    aesop (config := { terminal := false }) <;> omega
  have hc := M5.ConditionalCount.exact_completion_C N w F {0} {0}
    (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N)
    hN hF hFd hprefix
  have hp := M5.OrderCount.exact_C N w F hN hw hF hFd
  have he : M5.ConditionalCount.validCompletions N w F {0} {0}
      (M5.OrderCount.positivePositions N) (M5.OrderCount.positivePositions N) =
      M5.OrderCount.validPairs N w F := by
    ext UV
    simp [M5.ConditionalCount.validCompletions, M5.OrderCount.validPairs,
      Finset.singleton_union]
    intro hU hcU hV hcV
    have h0U : 0 ∉ UV.1 := by
      intro hz
      have hz' := hU hz
      simp [M5.OrderCount.positivePositions] at hz'
    have h0V : 0 ∉ UV.2 := by
      intro hz
      have hz' := hV hz
      simp [M5.OrderCount.positivePositions] at hz'
    have cU : (insert 0 UV.1).card = w := by
      rw [Finset.card_insert_of_notMem h0U, hcU]
      omega
    have cV : (insert 0 UV.2).card = w := by
      rw [Finset.card_insert_of_notMem h0V, hcV]
      omega
    simp [cU,cV]
  simpa [M5.PhysicalRecovery.oracle, M5.PhysicalRecovery.selectedA,
    M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.availableA,
    M5.PhysicalRecovery.availableB, hs, ha, he, hp, hw, hN] using hc

theorem M5.PhysicalRecovery.overfull_prefix_zero : ∀ (N w : ℕ) (F : M5.BinaryPolynomial) (p : List Bool), 0 < N → p.length ≤ M5.PhysicalRecovery.decisionCount N → (w < (M5.PhysicalRecovery.selectedA N p).card ∨ w < (M5.PhysicalRecovery.selectedB N p).card) → M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p = 0 := by
  intro N w F p hN hp hover
  classical
  have hnone : ∀ q ∈ M5.PhysicalRecovery.validWords N w F, ¬ p.IsPrefix q := by
    intro q hq hpq
    have hv : M5.PhysicalRecovery.wordValid N w F q :=
      (Finset.mem_filter.mp hq).2
    unfold M5.PhysicalRecovery.wordValid M5.PhysicalRecovery.ValidSupports at hv
    have hlen : q.length = M5.PhysicalRecovery.decisionCount N := by tauto
    have hA : (M5.PhysicalRecovery.selectedA N q).card = w := by tauto
    have hB : (M5.PhysicalRecovery.selectedB N q).card = w := by tauto
    have hs := (M5.PhysicalRecovery.prefix_extension N p q hN hp hlen).mp hpq
    have hcA := Finset.card_le_card hs.1
    have hcB := Finset.card_le_card hs.2.2.1
    omega
  unfold M5.PrefixPartition.count
  simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact hnone

theorem M5.PhysicalRecovery.semantic_completion_count : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length ≤ M5.PhysicalRecovery.decisionCount N → (M5.PhysicalRecovery.selectedA N p).card ≤ w → (M5.PhysicalRecovery.selectedB N p).card ≤ w → M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p = (M5.PhysicalRecovery.completionSet N w F p).card := by
  classical
  intro N w F hN hw hF hFN p hp hpa hpb
  let A := M5.PhysicalRecovery.selectedA N p
  let B := M5.PhysicalRecovery.selectedB N p
  let WA := M5.PhysicalRecovery.availableA N p
  let WB := M5.PhysicalRecovery.availableB N p
  let R := fun X Y : Finset ℕ =>
    M5.Connectivity.supportGcd N X Y = 1 ∧
    M5.completeSignature (M5.SupportPolynomial.ofSupport X)
      (M5.SupportPolynomial.ofSupport Y) N = F
  have hs := M5.PhysicalRecovery.state_domains N p hN hp
  have hA : A ⊆ Finset.range N := by
    dsimp [A]
    unfold M5.PhysicalRecovery.StateOK at hs
    aesop
  have hB : B ⊆ Finset.range N := by
    dsimp [B]
    unfold M5.PhysicalRecovery.StateOK at hs
    aesop
  have hWA : WA ⊆ Finset.range N := by
    dsimp [WA]
    unfold M5.PhysicalRecovery.StateOK at hs
    simp_all only [Finset.subset_iff, Finset.mem_sdiff]
    aesop
  have hWB : WB ⊆ Finset.range N := by
    dsimp [WB]
    unfold M5.PhysicalRecovery.StateOK at hs
    simp_all only [Finset.subset_iff, Finset.mem_sdiff]
    aesop
  have hA0 : 0 ∈ A := by
    simp [A, M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selected]
  have hB0 : 0 ∈ B := by
    simp [B, M5.PhysicalRecovery.selectedB, M5.PhysicalRecovery.selected]
  have hdA : Disjoint A WA := by
    dsimp [A, WA]
    unfold M5.PhysicalRecovery.StateOK at hs
    aesop
  have hdB : Disjoint B WB := by
    dsimp [B, WB]
    unfold M5.PhysicalRecovery.StateOK at hs
    aesop
  have words (q : List Bool) :
      q ∈ M5.PhysicalRecovery.validWords N w F ↔
        q.length = M5.PhysicalRecovery.decisionCount N ∧
        M5.PhysicalRecovery.ValidSupports N w F
          (M5.PhysicalRecovery.selectedA N q)
          (M5.PhysicalRecovery.selectedB N q) := by
    constructor
    · intro hq
      simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter,
        Finset.mem_image, Finset.mem_univ, true_and] at hq
      aesop (add simp [M5.PhysicalRecovery.wordValid])
    · intro hq
      let f : Fin (M5.PhysicalRecovery.decisionCount N) → Bool :=
        fun i => q[i.val]'(by omega)
      have hf : List.ofFn f = q := by
        apply List.ext_getElem
        · simpa using hq.1.symm
        · intro i hi hj
          simp [f]
      have hv : M5.PhysicalRecovery.wordValid N w F q := by
        simpa [M5.PhysicalRecovery.wordValid] using hq
      simp only [M5.PhysicalRecovery.validWords, Finset.mem_filter,
        Finset.mem_image, Finset.mem_univ, true_and]
      aesop
  have completions (U V : Finset ℕ) :
      (U, V) ∈ M5.PhysicalRecovery.completionSet N w F p ↔
        (U ⊆ WA ∧ U.card = w - A.card) ∧
        (V ⊆ WB ∧ V.card = w - B.card) ∧ R (A ∪ U) (B ∪ V) := by
    simp only [M5.PhysicalRecovery.completionSet,
      M5.ConditionalCount.validCompletions, Finset.product_eq_sprod,
      Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
    change (((U ⊆ WA ∧ U.card = w - A.card) ∧ (V ⊆ WB ∧ V.card = w - B.card)) ∧
      (A ∪ U).card = w ∧ (B ∪ V).card = w ∧ R (A ∪ U) (B ∪ V)) ↔
      (U ⊆ WA ∧ U.card = w - A.card) ∧ (V ⊆ WB ∧ V.card = w - B.card) ∧ R (A ∪ U) (B ∪ V)
    constructor
    · rintro ⟨⟨hu, hv⟩, _, _, hr⟩
      exact ⟨hu, hv, hr⟩
    · rintro ⟨hu, hv, hr⟩
      have hauc : (A ∪ U).card = w := by
        rw [Finset.card_union_of_disjoint (hdA.mono_right hu.1), hu.2]
        exact Nat.add_sub_of_le hpa
      have hbvc : (B ∪ V).card = w := by
        rw [Finset.card_union_of_disjoint (hdB.mono_right hv.1), hv.2]
        exact Nat.add_sub_of_le hpb
      exact ⟨⟨hu, hv⟩, hauc, hbvc, hr⟩
  have restore {S T : Finset ℕ} (h : S ⊆ T) : S ∪ (T \ S) = T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hx | ⟨hx, _⟩)
      · exact h hx
      · exact hx
    · intro hx
      by_cases hxS : x ∈ S
      · exact Or.inl hxS
      · exact Or.inr ⟨hx, hxS⟩
  have tail_subset {S T W : Finset ℕ} (h : T ⊆ S ∪ W) : T \ S ⊆ W := by
    intro x hx
    obtain ⟨hxT, hxS⟩ := Finset.mem_sdiff.mp hx
    exact (Finset.mem_union.mp (h hxT)).resolve_left hxS
  have remove {S U W : Finset ℕ} (hd : Disjoint S W) (hu : U ⊆ W) :
      (S ∪ U) \ S = U := by
    ext x
    have hh := Finset.disjoint_left.mp hd
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact False.elim (hn hx)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun hxS => hh hxS (hu hx)⟩
  let W := (M5.PhysicalRecovery.validWords N w F).filter (fun q => p.IsPrefix q)
  have member (q : List Bool) : q ∈ W ↔
      q.length = M5.PhysicalRecovery.decisionCount N ∧
      M5.PhysicalRecovery.ValidSupports N w F
        (M5.PhysicalRecovery.selectedA N q)
        (M5.PhysicalRecovery.selectedB N q) ∧ p.IsPrefix q := by
    simp only [W, Finset.mem_filter, words, and_assoc]
  let toTail := fun q : List Bool =>
    (M5.PhysicalRecovery.selectedA N q \ A,
     M5.PhysicalRecovery.selectedB N q \ B)
  have forward (q : List Bool) (hq : q ∈ W) :
      toTail q ∈ M5.PhysicalRecovery.completionSet N w F p := by
    obtain ⟨hql, hqv, hpre⟩ := (member q).mp hq
    obtain ⟨ha, hau, hb, hbu⟩ :=
      (M5.PhysicalRecovery.prefix_extension N p q hN hp hql).mp hpre
    change A ⊆ M5.PhysicalRecovery.selectedA N q at ha
    change B ⊆ M5.PhysicalRecovery.selectedB N q at hb
    have hca : (M5.PhysicalRecovery.selectedA N q).card = w := by
      unfold M5.PhysicalRecovery.ValidSupports at hqv
      aesop
    have hcb : (M5.PhysicalRecovery.selectedB N q).card = w := by
      unfold M5.PhysicalRecovery.ValidSupports at hqv
      aesop
    have hr : R (M5.PhysicalRecovery.selectedA N q)
        (M5.PhysicalRecovery.selectedB N q) := by
      dsimp [R]
      unfold M5.PhysicalRecovery.ValidSupports at hqv
      aesop
    apply (completions _ _).mpr
    refine ⟨⟨tail_subset hau, ?_⟩, ⟨tail_subset hbu, ?_⟩, ?_⟩
    · rw [Finset.card_sdiff_of_subset ha, hca]
    · rw [Finset.card_sdiff_of_subset hb, hcb]
    · simpa only [restore ha, restore hb] using hr
  have inverse (U V : Finset ℕ)
      (huv : (U, V) ∈ M5.PhysicalRecovery.completionSet N w F p) :
      let q := M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)
      q ∈ W ∧ toTail q = (U, V) := by
    obtain ⟨⟨hu, huc⟩, ⟨hv, hvc⟩, hr⟩ := (completions U V).mp huv
    have hAU : A ∪ U ⊆ Finset.range N :=
      Finset.union_subset hA (Finset.Subset.trans hu hWA)
    have hBV : B ∪ V ⊆ Finset.range N :=
      Finset.union_subset hB (Finset.Subset.trans hv hWB)
    have hAU0 : 0 ∈ A ∪ U := Finset.mem_union_left _ hA0
    have hBV0 : 0 ∈ B ∪ V := Finset.mem_union_left _ hB0
    have hdu : Disjoint A U := hdA.mono_right hu
    have hdv : Disjoint B V := hdB.mono_right hv
    have hauc : (A ∪ U).card = w := by
      rw [Finset.card_union_of_disjoint hdu, huc]
      exact Nat.add_sub_of_le hpa
    have hbvc : (B ∪ V).card = w := by
      rw [Finset.card_union_of_disjoint hdv, hvc]
      exact Nat.add_sub_of_le hpb
    let q := M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V)
    have hdecode := M5.PhysicalRecovery.decode_encode N (A ∪ U) (B ∪ V)
      hN hAU hBV hAU0 hBV0
    have hqa : M5.PhysicalRecovery.selectedA N q = A ∪ U := hdecode.1
    have hqb : M5.PhysicalRecovery.selectedB N q = B ∪ V := hdecode.2
    have hql : q.length = M5.PhysicalRecovery.decisionCount N := by
      simp only [q, M5.PhysicalRecovery.encode, List.length_ofFn]
    have hqv : M5.PhysicalRecovery.ValidSupports N w F
        (M5.PhysicalRecovery.selectedA N q)
        (M5.PhysicalRecovery.selectedB N q) := by
      rw [hqa, hqb]
      unfold M5.PhysicalRecovery.ValidSupports
      dsimp [R] at hr
      exact ⟨hAU, hBV, hAU0, hBV0, hauc, hbvc, hr⟩
    have hpre : p.IsPrefix q := by
      apply (M5.PhysicalRecovery.prefix_extension N p q hN hp hql).mpr
      rw [hqa, hqb]
      change A ⊆ A ∪ U ∧ A ∪ U ⊆ A ∪ WA ∧
        B ⊆ B ∪ V ∧ B ∪ V ⊆ B ∪ WB
      refine ⟨Finset.subset_union_left, ?_, Finset.subset_union_left, ?_⟩
      · exact Finset.union_subset_union (Finset.Subset.refl _) hu
      · exact Finset.union_subset_union (Finset.Subset.refl _) hv
    refine ⟨(member q).mpr ⟨hql, hqv, hpre⟩, ?_⟩
    change (M5.PhysicalRecovery.selectedA N q \ A,
      M5.PhysicalRecovery.selectedB N q \ B) = (U, V)
    rw [hqa, hqb, remove hdA hu, remove hdB hv]
  have hc : W.card = (M5.PhysicalRecovery.completionSet N w F p).card := by
    apply Finset.card_bij (fun q _ => toTail q)
    · exact forward
    · intro q hq r hr he
      obtain ⟨hql, hqv, hqp⟩ := (member q).mp hq
      obtain ⟨hrl, hrv, hrp⟩ := (member r).mp hr
      have hqe := (M5.PhysicalRecovery.prefix_extension N p q hN hp hql).mp hqp
      have hre := (M5.PhysicalRecovery.prefix_extension N p r hN hp hrl).mp hrp
      have hea := congrArg Prod.fst he
      have heb := congrArg Prod.snd he
      change M5.PhysicalRecovery.selectedA N q \ A =
        M5.PhysicalRecovery.selectedA N r \ A at hea
      change M5.PhysicalRecovery.selectedB N q \ B =
        M5.PhysicalRecovery.selectedB N r \ B at heb
      have ha : M5.PhysicalRecovery.selectedA N q =
          M5.PhysicalRecovery.selectedA N r := by
        calc
          _ = A ∪ (M5.PhysicalRecovery.selectedA N q \ A) := (restore hqe.1).symm
          _ = A ∪ (M5.PhysicalRecovery.selectedA N r \ A) := by rw [hea]
          _ = _ := restore hre.1
      have hb : M5.PhysicalRecovery.selectedB N q =
          M5.PhysicalRecovery.selectedB N r := by
        calc
          _ = B ∪ (M5.PhysicalRecovery.selectedB N q \ B) := (restore hqe.2.2.1).symm
          _ = B ∪ (M5.PhysicalRecovery.selectedB N r \ B) := by rw [heb]
          _ = _ := restore hre.2.2.1
      calc
        q = M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N q)
          (M5.PhysicalRecovery.selectedB N q) :=
            (M5.PhysicalRecovery.encode_decode N q hN hql).symm
        _ = M5.PhysicalRecovery.encode N (M5.PhysicalRecovery.selectedA N r)
          (M5.PhysicalRecovery.selectedB N r) := by rw [ha, hb]
        _ = r := M5.PhysicalRecovery.encode_decode N r hN hrl
    · rintro ⟨U, V⟩ huv
      obtain ⟨hq, he⟩ := inverse U V huv
      exact ⟨M5.PhysicalRecovery.encode N (A ∪ U) (B ∪ V), hq, he⟩
  have hcount : M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p = (W.card : ℤ) := by
    unfold M5.PrefixPartition.count
    apply congrArg (fun s : Finset (List Bool) => (s.card : ℤ))
    ext q
    simp only [W, Finset.mem_filter]
  rw [hcount]
  exact congrArg (fun n : ℕ => (n : ℤ)) hc

theorem M5.PhysicalRecovery.arithmetic_oracle_exact : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length ≤ M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.oracle N w F p = M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length ≤ M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.oracle N w F p = M5.PrefixPartition.count (M5.PhysicalRecovery.validWords N w F) p
  intro N w F hN hw hF hFN p hp
  have hs := M5.PhysicalRecovery.state_domains N p hN hp
  by_cases hpa : (M5.PhysicalRecovery.selectedA N p).card ≤ w
  · by_cases hpb : (M5.PhysicalRecovery.selectedB N p).card ≤ w
    · have hOK : M5.ConditionalCount.PrefixOK N w
          (M5.PhysicalRecovery.selectedA N p) (M5.PhysicalRecovery.selectedB N p)
          (M5.PhysicalRecovery.availableA N p) (M5.PhysicalRecovery.availableB N p) := by
        unfold M5.PhysicalRecovery.StateOK at hs
        unfold M5.ConditionalCount.PrefixOK
        aesop
      rw [M5.PhysicalRecovery.semantic_completion_count N w F hN hw hF hFN p hp hpa hpb]
      simpa [M5.PhysicalRecovery.oracle, M5.PhysicalRecovery.completionSet,
        hp, hs, hpa, hpb, hN, hw, hF, hFN, hOK, Nat.ne_of_gt hN, Nat.ne_of_gt hw]
        using M5.ConditionalCount.exact_completion_C N w F
          (M5.PhysicalRecovery.selectedA N p) (M5.PhysicalRecovery.selectedB N p)
          (M5.PhysicalRecovery.availableA N p) (M5.PhysicalRecovery.availableB N p)
          hN hF hFN hOK
    · rw [M5.PhysicalRecovery.overfull_prefix_zero N w F p hN hp
        (Or.inr (Nat.lt_of_not_ge hpb))]
      simp [M5.PhysicalRecovery.oracle, M5.ConditionalCount.completionC,
        hp, hs, hpa, hpb, hN, hw, hF, hFN]
  · rw [M5.PhysicalRecovery.overfull_prefix_zero N w F p hN hp
      (Or.inl (Nat.lt_of_not_ge hpa))]
    simp [M5.PhysicalRecovery.oracle, M5.ConditionalCount.completionC,
      hp, hs, hpa, hN, hw, hF, hFN]

theorem M5.PhysicalRecovery.actual_split : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length < M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.oracle N w F p = M5.PhysicalRecovery.oracle N w F (p ++ [false]) + M5.PhysicalRecovery.oracle N w F (p ++ [true]) := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length < M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.oracle N w F p = M5.PhysicalRecovery.oracle N w F (p ++ [false]) + M5.PhysicalRecovery.oracle N w F (p ++ [true])
  intro N w F hN hw hF hFN p hp
  have hchild (b : Bool) : (p ++ [b]).length ≤ M5.PhysicalRecovery.decisionCount N := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [M5.PhysicalRecovery.arithmetic_oracle_exact N w F hN hw hF hFN p (Nat.le_of_lt hp),
    M5.PhysicalRecovery.arithmetic_oracle_exact N w F hN hw hF hFN (p ++ [false]) (hchild false),
    M5.PhysicalRecovery.arithmetic_oracle_exact N w F hN hw hF hFN (p ++ [true]) (hchild true)]
  simpa [Fintype.sum_bool, add_comm] using
    (M5.PrefixPartition.count_partition Bool (M5.PhysicalRecovery.validWords N w F)
      (M5.PhysicalRecovery.decisionCount N) p
      (fun q hq => M5.PhysicalRecovery.valid_words_length N w F q hq) hp)

theorem M5.PhysicalRecovery.actual_terminal : ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length = M5.PhysicalRecovery.decisionCount N → 0 < M5.PhysicalRecovery.oracle N w F p → M5.PhysicalRecovery.wordValid N w F p := by
  classical
  change ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → ∀ p : List Bool, p.length = M5.PhysicalRecovery.decisionCount N → 0 < M5.PhysicalRecovery.oracle N w F p → M5.PhysicalRecovery.wordValid N w F p
  intro N w F hN hw hF hFN p hp hpos
  rw [M5.PhysicalRecovery.arithmetic_oracle_exact N w F hN hw hF hFN p hp.le] at hpos
  rw [M5.PrefixPartition.count_terminal Bool (M5.PhysicalRecovery.validWords N w F)
    (M5.PhysicalRecovery.decisionCount N) p
    (fun q hq => M5.PhysicalRecovery.valid_words_length N w F q hq) hp] at hpos
  by_cases hm : p ∈ M5.PhysicalRecovery.validWords N w F
  · exact (Finset.mem_filter.mp hm).2
  · simp [hm] at hpos
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) (F : M5.BinaryPolynomial), 0 < N → 0 < w → F.Monic → F ∣ M5.cyclicModulus N → 0 < M5.OrderCount.C N w F → M5.PhysicalRecovery.wordValid N w F (M5.PhysicalRecovery.recoverWord N w F)
