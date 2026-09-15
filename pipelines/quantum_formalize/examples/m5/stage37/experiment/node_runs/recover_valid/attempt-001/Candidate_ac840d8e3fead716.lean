import FrozenTarget_ac840d8e3fead716
theorem M5.ResidueRecovery.recover_valid : QuantumHarnessFrozenTarget := by
  change ∀ (T : ℕ) (c : List (Fin T) → ℤ) (Valid : List (Fin T) → Prop) (m : ℕ), (∀ q : List (Fin T), q.length < m → c q = ∑ a : Fin T, c (q ++ [a])) → (∀ q : List (Fin T), q.length = m → 0 < c q → Valid q) → 0 < c [] → ∃ q : List (Fin T), (M5.ResidueRecovery.recover c [] m).1 = some q ∧ q.length = m ∧ Valid q ∧ (M5.ResidueRecovery.recover c [] m).2 ≤ m * T
  intro T c Valid m hpart hvalid hpos
  have hpart' : ∀ q : List (Fin T), q.length < ([] : List (Fin T)).length + m → c q = ∑ a : Fin T, c (q ++ [a]) := by
    simpa only [List.length_nil, Nat.zero_add] using hpart
  obtain ⟨q, hq, hlen, hpositive, hcost⟩ :=
    M5.ResidueRecovery.recover_success T c [] m hpart' hpos
  have hlen' : q.length = m := by
    simpa only [List.length_nil, Nat.zero_add] using hlen
  exact ⟨q, hq, hlen', hvalid q hlen' hpositive, hcost⟩
