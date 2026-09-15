import FrozenTarget_970a6170f12238e6
theorem M5.ResidueRecovery.recover_success : QuantumHarnessFrozenTarget := by
  change ∀ (T : ℕ) (c : List (Fin T) → ℤ) (p : List (Fin T)) (n : ℕ), (∀ q : List (Fin T), q.length < p.length + n → c q = ∑ a : Fin T, c (q ++ [a])) → 0 < c p → ∃ q : List (Fin T), (M5.ResidueRecovery.recover c p n).1 = some q ∧ q.length = p.length + n ∧ 0 < c q ∧ (M5.ResidueRecovery.recover c p n).2 ≤ n * T
  intro T c p n
  induction n generalizing p with
  | zero =>
      intro hpart hpos
      exact ⟨p, by simp [M5.ResidueRecovery.recover], by simp, hpos, by simp [M5.ResidueRecovery.recover]⟩
  | succ n ih =>
      intro hpart hpos
      have hsum : 0 < ∑ a : Fin T, c (p ++ [a]) := by
        rw [← hpart p (by omega)]
        exact hpos
      have hex : ∃ a : Fin T, 0 < c (p ++ [a]) := by
        by_contra h
        push_neg at h
        have hn : (∑ a : Fin T, c (p ++ [a])) ≤ 0 :=
          Finset.sum_nonpos (fun a _ => h a)
        omega
      have hexList : ∃ a ∈ List.finRange T, 0 < c (p ++ [a]) := by
        obtain ⟨a, ha⟩ := hex
        exact ⟨a, by simp, ha⟩
      obtain ⟨a, _, hpick, ha⟩ :=
        M5.ResidueRecovery.pick_positive T (fun a => c (p ++ [a])) (List.finRange T) hexList
      let k := (M5.ResidueRecovery.pick (fun a => c (p ++ [a])) (List.finRange T)).2
      have hk : k ≤ T := by
        simpa [k] using M5.ResidueRecovery.pick_bound T (fun a => c (p ++ [a])) (List.finRange T)
      have hpfull : M5.ResidueRecovery.pick (fun a => c (p ++ [a])) (List.finRange T) = (some a, k) :=
        Prod.ext hpick rfl
      have hpart' : ∀ q : List (Fin T), q.length < (p ++ [a]).length + n → c q = ∑ b : Fin T, c (q ++ [b]) := by
        intro q hq
        apply hpart q
        simp only [List.length_append, List.length_singleton] at hq
        omega
      obtain ⟨q, hq, hlen, hpositive, hcost⟩ := ih (p ++ [a]) hpart' ha
      let d := (M5.ResidueRecovery.recover c (p ++ [a]) n).2
      have hrfull : M5.ResidueRecovery.recover c (p ++ [a]) n = (some q, d) :=
        Prod.ext hq rfl
      have hfull : M5.ResidueRecovery.recover c p (n + 1) = (some q, k + d) := by
        rw [M5.ResidueRecovery.recover, hpfull]
        simp only [Prod.fst, Prod.snd, hrfull]
      refine ⟨q, ?_, ?_, hpositive, ?_⟩
      · rw [hfull]
      · simp only [List.length_append, List.length_singleton] at hlen
        omega
      · rw [hfull]
        change k + d ≤ (n + 1) * T
        have hd : d ≤ n * T := hcost
        rw [Nat.add_mul, Nat.one_mul]
        omega
