import FrozenTarget_311fef136d11d5ac
theorem M5.ResidueRecovery.recover_success : QuantumHarnessFrozenTarget := by
  change ∀ (T : ℕ) (c : List (Fin T) → ℤ) (p : List (Fin T)) (n : ℕ), (∀ q : List (Fin T), q.length < p.length + n → c q = ∑ a : Fin T, c (q ++ [a])) → 0 < c p → ∃ q : List (Fin T), (M5.ResidueRecovery.recover c p n).1 = some q ∧ q.length = p.length + n ∧ 0 < c q ∧ (M5.ResidueRecovery.recover c p n).2 ≤ n * T
  intro T c p n
  induction n generalizing p with
  | zero =>
      intro hpart hpos
      exact ⟨p, by simp [M5.ResidueRecovery.recover], by simp, hpos, by simp [M5.ResidueRecovery.recover]⟩
  | succ n ih =>
      intro hpart hpos
      have hex : ∃ a : Fin T, 0 < c (p ++ [a]) := by
        by_contra hn
        push_neg at hn
        have hs : (∑ a : Fin T, c (p ++ [a])) ≤ 0 :=
          Finset.sum_nonpos (fun a _ => hn a)
        have he := hpart p (by omega)
        omega
      have hmem : ∃ a ∈ List.finRange T, 0 < c (p ++ [a]) := by
        obtain ⟨a, ha⟩ := hex
        exact ⟨a, by simp, ha⟩
      obtain ⟨a, ha, hpick, hapos⟩ :=
        M5.ResidueRecovery.pick_positive T (fun a => c (p ++ [a])) (List.finRange T) hmem
      have hcost : (M5.ResidueRecovery.pick (fun a => c (p ++ [a])) (List.finRange T)).2 ≤ T := by
        simpa using M5.ResidueRecovery.pick_bound T (fun a => c (p ++ [a])) (List.finRange T)
      have hpick' : M5.ResidueRecovery.pick (fun a => c (p ++ [a])) (List.finRange T) =
          (some a, (M5.ResidueRecovery.pick (fun a => c (p ++ [a])) (List.finRange T)).2) :=
        Prod.ext hpick rfl
      have hpart' : ∀ q : List (Fin T), q.length < (p ++ [a]).length + n → c q = ∑ b : Fin T, c (q ++ [b]) := by
        intro q hq
        apply hpart q
        simp only [List.length_append, List.length_singleton] at hq
        omega
      obtain ⟨q, hq, hlen, hqpos, hbound⟩ := ih (p ++ [a]) hpart' hapos
      have hrec : M5.ResidueRecovery.recover c (p ++ [a]) n =
          (some q, (M5.ResidueRecovery.recover c (p ++ [a]) n).2) :=
        Prod.ext hq rfl
      refine ⟨q, ?_, ?_, hqpos, ?_⟩
      · simp only [M5.ResidueRecovery.recover, hpick', hrec, Prod.fst, Prod.snd]
      · simp only [List.length_append, List.length_singleton] at hlen
        omega
      · have hb := Nat.add_le_add hcost hbound
        simp only [M5.ResidueRecovery.recover, hpick', hrec, Prod.fst, Prod.snd]
        rw [Nat.succ_mul]
        omega
