import M5ResidueRecovery

theorem M5.ResidueRecovery.pick_bound : ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (M5.ResidueRecovery.pick f xs).2 ≤ xs.length := by
  change ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (M5.ResidueRecovery.pick f xs).2 ≤ xs.length
  intro T f xs
  induction xs with
  | nil => simp [M5.ResidueRecovery.pick]
  | cons x xs ih =>
      simp only [M5.ResidueRecovery.pick, List.length_cons]
      split
      · simp
      · cases h : M5.ResidueRecovery.pick f xs with
        | mk result cost =>
            simp_all only [Prod.snd] <;> omega

theorem M5.ResidueRecovery.pick_positive : ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (∃ a ∈ xs, 0 < f a) → ∃ a ∈ xs, (M5.ResidueRecovery.pick f xs).1 = some a ∧ 0 < f a := by
  change ∀ (T : ℕ) (f : Fin T → ℤ) (xs : List (Fin T)), (∃ a ∈ xs, 0 < f a) → ∃ a ∈ xs, (M5.ResidueRecovery.pick f xs).1 = some a ∧ 0 < f a
  intro T f xs
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      intro hex
      by_cases hx : 0 < f x
      · refine ⟨x, List.mem_cons_self, ?_, hx⟩
        simp [M5.ResidueRecovery.pick, hx]
      · have htail : ∃ a ∈ xs, 0 < f a := by
          obtain ⟨a, ha, hpos⟩ := hex
          rcases List.mem_cons.mp ha with hax | ha
          · subst a
            exact (hx hpos).elim
          · exact ⟨a, ha, hpos⟩
        obtain ⟨a, ha, heq, hpos⟩ := ih htail
        refine ⟨a, List.mem_cons_of_mem x ha, ?_, hpos⟩
        cases hp : M5.ResidueRecovery.pick f xs with
        | mk o n =>
            simpa [M5.ResidueRecovery.pick, hx, hp] using heq
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T : ℕ) (c : List (Fin T) → ℤ) (p : List (Fin T)) (n : ℕ), (∀ q : List (Fin T), q.length < p.length + n → c q = ∑ a : Fin T, c (q ++ [a])) → 0 < c p → ∃ q : List (Fin T), (M5.ResidueRecovery.recover c p n).1 = some q ∧ q.length = p.length + n ∧ 0 < c q ∧ (M5.ResidueRecovery.recover c p n).2 ≤ n * T
