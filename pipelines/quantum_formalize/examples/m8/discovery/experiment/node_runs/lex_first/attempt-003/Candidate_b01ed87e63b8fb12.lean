import FrozenTarget_b01ed87e63b8fb12
theorem M8.Discovery.lex_first : QuantumHarnessFrozenTarget := by
  classical
  intro N _ c k h j hj
  rcases j with ⟨je, jt, ja, jb⟩
  have present (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (i : Fin n) (hi : f i ≠ none) :
      (M8.FiniteSearch.find f).1.map Prod.snd ≠ none := by
    intro hm
    have hf : (M8.FiniteSearch.find f).1 = none := by
      cases hh : (M8.FiniteSearch.find f).1 with
      | none => rfl
      | some p => simp [hh] at hm
    exact hi ((M8.FiniteSearch.find_none n (M8.Discovery.Choice N) f).mp hf i)
  have step (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (hs : (M8.FiniteSearch.find f).1.map Prod.snd = some k) :
      ∃ i, f i = some k ∧ ∀ j, f j ≠ none → i ≤ j := by
    cases hf : (M8.FiniteSearch.find f).1 with
    | none => simp [hf] at hs
    | some p =>
      rcases p with ⟨i, v⟩
      have hv : v = k := by simpa [hf] using hs
      subst v
      have hh := (M8.FiniteSearch.find_some n (M8.Discovery.Choice N) f i k).mp hf
      refine ⟨i, hh.1, ?_⟩
      intro j hn
      apply le_of_not_gt
      intro hlt
      exact hn (hh.2 j hlt)
  obtain ⟨ej, hej⟩ : ∃ ej : Fin 2, decide (ej.val = 1) = je := by
    cases je
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
  have hjtest : M8.Discovery.test c ⟨je, jt, ja, jb⟩ = true :=
    (M8.Discovery.test_spec N c ⟨je, jt, ja, jb⟩).mpr hj
  have hleaf :
      (if M8.Discovery.test c ⟨decide (ej.val = 1), jt, ja, jb⟩ = true then
        some (⟨decide (ej.val = 1), jt, ja, jb⟩ : M8.Discovery.Choice N)
      else none) ≠ none := by
    rw [hej]
    simp [hjtest]
  have hr : M8.Discovery.atRight c (decide (ej.val = 1)) jt ja ≠ none := by
    unfold M8.Discovery.atRight
    exact present N _ jb hleaf
  have hl : M8.Discovery.atLeft c (decide (ej.val = 1)) jt ≠ none := by
    unfold M8.Discovery.atLeft
    exact present N _ ja hr
  have hu : M8.Discovery.atUnit c (decide (ej.val = 1)) ≠ none := by
    unfold M8.Discovery.atUnit
    exact present N _ jt hl
  unfold M8.Discovery.discover at h
  obtain ⟨e, he, emin⟩ := step 2 _ h
  unfold M8.Discovery.atUnit at he
  obtain ⟨t, ht, tmin⟩ := step N _ he
  unfold M8.Discovery.atLeft at ht
  obtain ⟨a, ha, amin⟩ := step N _ ht
  unfold M8.Discovery.atRight at ha
  obtain ⟨b, hb, bmin⟩ := step N _ ha
  change (if M8.Discovery.test c ⟨decide (e.val = 1), t, a, b⟩ = true then
    some ⟨decide (e.val = 1), t, a, b⟩ else none) = some k at hb
  have hk : (⟨decide (e.val = 1), t, a, b⟩ : M8.Discovery.Choice N) = k := by
    by_cases hp : M8.Discovery.test c ⟨decide (e.val = 1), t, a, b⟩ = true
    · simpa [hp] using hb
    · simp [hp] at hb
  subst k
  simp only [M8.Discovery.key, Prod.Lex.toLex_le_toLex]
  have hele : e ≤ ej := emin ej hu
  rcases lt_or_eq_of_le hele with helt | heeq
  · left
    rw [← hej]
    fin_cases e <;> fin_cases ej <;> norm_num at helt ⊢
  · subst e
    right
    refine ⟨hej, ?_⟩
    have ht_le : t ≤ jt := tmin jt hl
    rcases lt_or_eq_of_le ht_le with ht_lt | ht_eq
    · exact Or.inl ht_lt
    · subst t
      right
      refine ⟨rfl, ?_⟩
      have ha_le : a ≤ ja := amin ja hr
      rcases lt_or_eq_of_le ha_le with ha_lt | ha_eq
      · exact Or.inl ha_lt
      · subst a
        exact Or.inr ⟨rfl, bmin jb hleaf⟩
