import FrozenTarget_c294318ade28f5f6
theorem M8.Discovery.lex_first : QuantumHarnessFrozenTarget := by
  classical
  intro N _ c k hk j hj
  have step (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (h : (M8.FiniteSearch.find f).1.map Prod.snd = some k) :
      ∃ i, f i = some k ∧ ∀ q : Fin n, q.val < i.val → f q = none := by
    cases hf : (M8.FiniteSearch.find f).1 with
    | none => simp [hf] at h
    | some p =>
      rcases p with ⟨i, v⟩
      have hv : v = k := by simpa [hf] using h
      subst v
      exact ⟨i, (M8.FiniteSearch.find_some n (M8.Discovery.Choice N) f i k).mp hf⟩
  have present (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (i : Fin n) (hi : f i ≠ none) :
      (M8.FiniteSearch.find f).1.map Prod.snd ≠ none := by
    cases hf : (M8.FiniteSearch.find f).1 with
    | none =>
      exact False.elim (hi ((M8.FiniteSearch.find_none n (M8.Discovery.Choice N) f).mp hf i))
    | some p => simp [hf]
  have lower (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (i q : Fin n) (hm : ∀ q : Fin n, q.val < i.val → f q = none)
      (hq : f q ≠ none) : i ≤ q := by
    by_contra h
    have hlt : q < i := lt_of_not_ge h
    exact hq (hm q hlt)
  unfold M8.Discovery.discover at hk
  obtain ⟨e, he, hem⟩ := step 2 _ hk
  unfold M8.Discovery.atUnit at he
  obtain ⟨t, ht, htm⟩ := step N _ he
  unfold M8.Discovery.atLeft at ht
  obtain ⟨a, ha, ham⟩ := step N _ ht
  unfold M8.Discovery.atRight at ha
  obtain ⟨b, hb, hbm⟩ := step N _ ha
  change (if M8.Discovery.test c ⟨decide (e.val = 1), t, a, b⟩ = true then
    some ⟨decide (e.val = 1), t, a, b⟩ else none) = some k at hb
  have hchoice : (⟨decide (e.val = 1), t, a, b⟩ : M8.Discovery.Choice N) = k := by
    split at hb
    · exact Option.some.inj hb
    · cases hb
  subst k
  rcases j with ⟨je, jt, ja, jb⟩
  have hjtest := (M8.Discovery.test_spec N c ⟨je, jt, ja, jb⟩).mpr hj
  have hjb : (if M8.Discovery.test c ⟨je, jt, ja, jb⟩ = true then
      some (⟨je, jt, ja, jb⟩ : M8.Discovery.Choice N) else none) ≠ none := by
    simp [hjtest]
  have hja := present N (fun b : Fin N =>
    if M8.Discovery.test c ⟨je, jt, ja, b⟩ = true then
      some (⟨je, jt, ja, b⟩ : M8.Discovery.Choice N) else none) jb hjb
  change M8.Discovery.atRight c je jt ja ≠ none at hja
  have hjt := present N (fun a => M8.Discovery.atRight c je jt a) ja hja
  change M8.Discovery.atLeft c je jt ≠ none at hjt
  have hje := present N (fun t => M8.Discovery.atLeft c je t) jt hjt
  change M8.Discovery.atUnit c je ≠ none at hje
  let ej : Fin 2 := if je then 1 else 0
  have hej : decide (ej.val = 1) = je := by
    cases je <;> rfl
  have hejpresent : M8.Discovery.atUnit c (decide (ej.val = 1)) ≠ none := by
    simpa only [hej] using hje
  have hele := lower 2 _ e ej hem hejpresent
  have boolmono : ∀ x y : Fin 2, x ≤ y →
      decide (x.val = 1) ≤ decide (y.val = 1) := by decide
  have hebool : decide (e.val = 1) ≤ je := by
    simpa only [hej] using boolmono e ej hele
  rcases lt_or_eq_of_le hebool with helt | heeq
  · apply le_of_lt
    change toLex (decide (e.val = 1), toLex (t, toLex (a, b))) <
      toLex (je, toLex (jt, toLex (ja, jb)))
    apply Prod.Lex.left
    exact helt
  · subst je
    have htle := lower N _ t jt htm hjt
    rcases lt_or_eq_of_le htle with htlt | hteq
    · apply le_of_lt
      change toLex (decide (e.val = 1), toLex (t, toLex (a, b))) <
        toLex (decide (e.val = 1), toLex (jt, toLex (ja, jb)))
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact htlt
    · subst jt
      have hale := lower N _ a ja ham hja
      rcases lt_or_eq_of_le hale with halt | haeq
      · apply le_of_lt
        change toLex (decide (e.val = 1), toLex (t, toLex (a, b))) <
          toLex (decide (e.val = 1), toLex (t, toLex (ja, jb)))
        apply Prod.Lex.right
        apply Prod.Lex.right
        apply Prod.Lex.left
        exact halt
      · subst ja
        have hble := lower N _ b jb hbm hjb
        rcases lt_or_eq_of_le hble with hblt | hbeq
        · apply le_of_lt
          change toLex (decide (e.val = 1), toLex (t, toLex (a, b))) <
            toLex (decide (e.val = 1), toLex (t, toLex (a, jb)))
          apply Prod.Lex.right
          apply Prod.Lex.right
          apply Prod.Lex.right
          exact hblt
        · subst jb
          exact le_refl _
