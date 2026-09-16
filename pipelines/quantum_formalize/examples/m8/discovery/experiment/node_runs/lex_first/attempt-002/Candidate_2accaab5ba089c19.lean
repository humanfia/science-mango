import FrozenTarget_2accaab5ba089c19
theorem M8.Discovery.lex_first : QuantumHarnessFrozenTarget := by
  classical
  intro N _ c k h j hj
  have live (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (i : Fin n) (hi : f i ≠ none) :
      (M8.FiniteSearch.find f).1.map Prod.snd ≠ none := by
    cases hf : (M8.FiniteSearch.find f).1 with
    | none =>
      exact False.elim (hi ((M8.FiniteSearch.find_none n _ f).mp hf i))
    | some p => simp
  have step (n : ℕ) (f : Fin n → Option (M8.Discovery.Choice N))
      (hs : (M8.FiniteSearch.find f).1.map Prod.snd = some k) :
      ∃ i, f i = some k ∧ ∀ r, f r ≠ none → i ≤ r := by
    cases hf : (M8.FiniteSearch.find f).1 with
    | none => simp [hf] at hs
    | some p =>
      rcases p with ⟨i, v⟩
      have hv : v = k := by simpa [hf] using hs
      subst v
      obtain ⟨hi, hfirst⟩ := (M8.FiniteSearch.find_some n _ f i k).mp hf
      refine ⟨i, hi, ?_⟩
      intro r hr
      by_contra hn
      exact hr (hfirst r (by simpa using lt_of_not_ge hn))
  have htest := (M8.Discovery.test_spec N c j).mpr hj
  have hjR : M8.Discovery.atRight c j.exchange j.unitIndex j.leftAnchor ≠ none := by
    unfold M8.Discovery.atRight
    apply live N _ j.rightAnchor
    simpa [htest]
  have hjL : M8.Discovery.atLeft c j.exchange j.unitIndex ≠ none := by
    unfold M8.Discovery.atLeft
    exact live N _ j.leftAnchor hjR
  have hjU : M8.Discovery.atUnit c j.exchange ≠ none := by
    unfold M8.Discovery.atUnit
    exact live N _ j.unitIndex hjL
  unfold M8.Discovery.discover at h
  obtain ⟨e, he, hE⟩ := step 2 _ h
  unfold M8.Discovery.atUnit at he
  obtain ⟨t, ht, hT⟩ := step N _ he
  unfold M8.Discovery.atLeft at ht
  obtain ⟨a, ha, hA⟩ := step N _ ht
  unfold M8.Discovery.atRight at ha
  obtain ⟨b, hb, hB⟩ := step N _ ha
  change (if M8.Discovery.test c ⟨decide (e.val = 1), t, a, b⟩ = true then
    some ⟨decide (e.val = 1), t, a, b⟩ else none) = some k at hb
  have hk : (⟨decide (e.val = 1), t, a, b⟩ : M8.Discovery.Choice N) = k := by
    split at hb
    · exact Option.some.inj hb
    · contradiction
  rw [← hk]
  change toLex (decide (e.val = 1), toLex (t, toLex (a, b))) ≤
    toLex (j.exchange, toLex (j.unitIndex, toLex (j.leftAnchor, j.rightAnchor)))
  let q : Fin 2 := if j.exchange then 1 else 0
  have hq : decide (q.val = 1) = j.exchange := by
    cases hx : j.exchange <;> simp [q, hx]
  have heq : e ≤ q := hE q (by simpa only [hq] using hjU)
  rcases lt_or_eq_of_le heq with hel | heq
  · apply Prod.Lex.left
    fin_cases e <;> cases hx : j.exchange <;> norm_num [q, hx] at hel ⊢
  · have heB : decide (e.val = 1) = j.exchange := by
      rw [heq]
      exact hq
    rw [heB]
    apply Prod.Lex.right
    have htj : t ≤ j.unitIndex := hT j.unitIndex (by simpa only [heB] using hjL)
    rcases lt_or_eq_of_le htj with htl | hte
    · exact Prod.Lex.left _ _ htl
    · rw [hte]
      apply Prod.Lex.right
      have haj : a ≤ j.leftAnchor := hA j.leftAnchor (by
        simpa only [heB, hte] using hjR)
      rcases lt_or_eq_of_le haj with hal | hae
      · exact Prod.Lex.left _ _ hal
      · rw [hae]
        apply Prod.Lex.right
        apply hB j.rightAnchor
        simpa only [heB, hte, hae, htest, if_true] using
          (show (some j : Option (M8.Discovery.Choice N)) ≠ none by simp)
