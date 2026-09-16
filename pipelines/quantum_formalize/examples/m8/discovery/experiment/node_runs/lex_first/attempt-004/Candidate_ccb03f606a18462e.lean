import FrozenTarget_ccb03f606a18462e
theorem M8.Discovery.lex_first : QuantumHarnessFrozenTarget := by
  classical
  intro N _ c k h j hj
  have lift (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (i : Fin n) (hi : f i ≠ none) :
      (M8.FiniteSearch.find f).1.map Prod.snd ≠ none := by
    intro hz
    have hf : (M8.FiniteSearch.find f).1 = none := by
      cases hh : (M8.FiniteSearch.find f).1 <;> simp_all
    exact hi ((M8.FiniteSearch.find_none n (M8.Discovery.Choice N) f).mp hf i)
  have step (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (hs : (M8.FiniteSearch.find f).1.map Prod.snd = some k) :
      ∃ i, f i = some k ∧ ∀ q, f q ≠ none → i ≤ q := by
    cases hf : (M8.FiniteSearch.find f).1 with
    | none => simp [hf] at hs
    | some p =>
      rcases p with ⟨i, v⟩
      have hv : v = k := by simpa [hf] using hs
      subst v
      have hp := (M8.FiniteSearch.find_some n (M8.Discovery.Choice N) f i k).mp hf
      refine ⟨i, hp.1, ?_⟩
      intro q hq
      by_contra hn
      exact hq (hp.2 q (by omega))
  have hjtest := (M8.Discovery.test_spec N c j).mpr hj
  have hr : M8.Discovery.atRight c j.exchange j.unitIndex j.leftAnchor ≠ none := by
    unfold M8.Discovery.atRight
    apply lift N _ j.rightAnchor
    change (if M8.Discovery.test c j = true then some j else none) ≠ none
    simp [hjtest]
  have hl : M8.Discovery.atLeft c j.exchange j.unitIndex ≠ none := by
    unfold M8.Discovery.atLeft
    exact lift N _ j.leftAnchor hr
  have hu : M8.Discovery.atUnit c j.exchange ≠ none := by
    unfold M8.Discovery.atUnit
    exact lift N _ j.unitIndex hl
  let ej : Fin 2 := if j.exchange then 1 else 0
  have hej : decide (ej.val = 1) = j.exchange := by
    cases hx : j.exchange <;> simp [ej, hx]
  unfold M8.Discovery.discover at h
  obtain ⟨e, he, emin⟩ := step 2 _ h
  have ele : e ≤ ej := emin ej (by simpa only [hej] using hu)
  unfold M8.Discovery.atUnit at he
  obtain ⟨t, ht, tmin⟩ := step N _ he
  unfold M8.Discovery.atLeft at ht
  obtain ⟨a, ha, amin⟩ := step N _ ht
  unfold M8.Discovery.atRight at ha
  obtain ⟨b, hb, bmin⟩ := step N _ ha
  change (if M8.Discovery.test c ⟨decide (e.val = 1), t, a, b⟩ = true then
    some ⟨decide (e.val = 1), t, a, b⟩ else none) = some k at hb
  have hk : (⟨decide (e.val = 1), t, a, b⟩ : M8.Discovery.Choice N) = k := by
    split at hb
    · exact Option.some.inj hb
    · simp at hb
  rw [← hk]
  change toLex (decide (e.val = 1), toLex (t, toLex (a, b))) ≤
    toLex (j.exchange, toLex (j.unitIndex, toLex (j.leftAnchor, j.rightAnchor)))
  rcases lt_or_eq_of_le ele with elt | eeq
  · have hex : decide (e.val = 1) < j.exchange := by
      fin_cases e <;> cases hx : j.exchange <;> simp_all [ej]
    apply Prod.Lex.left
    exact hex
  · have hex : decide (e.val = 1) = j.exchange := by
      rw [eeq]
      exact hej
    rw [hex] at tmin amin bmin ⊢
    apply Prod.Lex.right
    have tle : t ≤ j.unitIndex := tmin j.unitIndex hl
    rcases lt_or_eq_of_le tle with tlt | teq
    · apply Prod.Lex.left
      exact tlt
    · subst t
      apply Prod.Lex.right
      have ale : a ≤ j.leftAnchor := amin j.leftAnchor hr
      rcases lt_or_eq_of_le ale with alt | aeq
      · apply Prod.Lex.left
        exact alt
      · subst a
        apply Prod.Lex.right
        apply bmin j.rightAnchor
        change (if M8.Discovery.test c j = true then some j else none) ≠ none
        simp [hjtest]
