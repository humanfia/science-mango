import M5ArithmeticResidueRecovery
import M5ConditionalResidueCountAccepted
import M5PrefixPartitionAccepted
import M5ResidueRecoveryAccepted

theorem M5.ArithmeticResidueRecovery.completion_word_split : ∀ {α : Type} (k : ℕ) (u : List α) (a : Fin (k - (u.take k).length) → α) (b : Fin (k - (u.drop k).length) → α), u.length ≤ 2*k → (M5.ArithmeticResidueRecovery.completionWord k u a b).length = 2*k ∧ u.IsPrefix (M5.ArithmeticResidueRecovery.completionWord k u a b) ∧ (M5.ArithmeticResidueRecovery.completionWord k u a b).take k = u.take k ++ List.ofFn a ∧ (M5.ArithmeticResidueRecovery.completionWord k u a b).drop k = u.drop k ++ List.ofFn b := by
  intro α k u a b hu
  have hta : (u.take k).length ≤ k := by simp only [List.length_take]; omega
  have hdb : (u.drop k).length ≤ k := by simp only [List.length_drop]; omega
  have hA : (u.take k ++ List.ofFn a).length = k := by
    simp only [List.length_append, List.length_ofFn]
    omega
  have hB : (u.drop k ++ List.ofFn b).length = k := by
    simp only [List.length_append, List.length_ofFn]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold M5.ArithmeticResidueRecovery.completionWord
    rw [List.length_append, hA, hB]
    omega
  · by_cases h : u.length ≤ k
    · have ht : u.take k = u := List.take_of_length_le h
      have hup : u.IsPrefix (u.take k) := by rw [ht]
      exact hup.trans ((List.prefix_append (u.take k) (List.ofFn a)).trans
        (List.prefix_append (u.take k ++ List.ofFn a) (u.drop k ++ List.ofFn b)))
    · have ht : (u.take k).length = k := by simp only [List.length_take]; omega
      have ha : List.ofFn a = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_ofFn, ht, Nat.sub_self]
      unfold M5.ArithmeticResidueRecovery.completionWord
      rw [ha, List.append_nil, ← List.append_assoc, List.take_append_drop]
      exact List.prefix_append u _
  · exact List.take_left' hA
  · exact List.drop_left' hA

theorem M5.ArithmeticResidueRecovery.prefix_algebra : ∀ (T k : ℕ) (p : List (Fin T)) (a : Fin k → Fin T), M5.ConditionalResidueCount.selectedPolynomial (p ++ List.ofFn a) = M5.ConditionalResidueCount.completedPolynomial (M5.ConditionalResidueCount.selectedPolynomial p) a ∧ M5.ConditionalResidueCount.prefixGcd (p ++ List.ofFn a) = Nat.gcd (M5.ConditionalResidueCount.prefixGcd p) (Finset.univ.gcd (fun i : Fin k => (a i).val)) := by
  intro T k p a
  classical
  constructor
  · simp [M5.ConditionalResidueCount.selectedPolynomial,
      M5.ConditionalResidueCount.completedPolynomial,
      List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
      add_assoc]
  · have hd : ∀ (l : List (Fin T)) (d : ℕ),
        d ∣ M5.ConditionalResidueCount.prefixGcd l ↔ ∀ r ∈ l, d ∣ r.val := by
      intro l d
      induction l with
      | nil => simp [M5.ConditionalResidueCount.prefixGcd]
      | cons r l ih =>
        simp_all [M5.ConditionalResidueCount.prefixGcd, Nat.dvd_gcd_iff]
    have he : ∀ d : ℕ,
        d ∣ M5.ConditionalResidueCount.prefixGcd (p ++ List.ofFn a) ↔
        d ∣ Nat.gcd (M5.ConditionalResidueCount.prefixGcd p)
          (Finset.univ.gcd (fun i : Fin k => (a i).val)) := by
      intro d
      rw [hd, Nat.dvd_gcd_iff, hd, Finset.dvd_gcd_iff]
      constructor
      · intro h
        constructor
        · intro r hr
          exact h r (List.mem_append.mpr (Or.inl hr))
        · intro i hi
          apply h (a i)
          apply List.mem_append.mpr
          exact Or.inr (by simp)
      · rintro ⟨hp, ha⟩ r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hp r hr
        · have hi : ∃ i, a i = r := by simpa using hr
          rcases hi with ⟨i, rfl⟩
          exact ha i (Finset.mem_univ i)
    apply Nat.dvd_antisymm
    · exact (he _).mp dvd_rfl
    · exact (he _).mpr dvd_rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (u : List (Fin T)) (a : Fin ((w-1) - (u.take (w-1)).length) → Fin T) (b : Fin ((w-1) - (u.drop (w-1)).length) → Fin T), u.length ≤ 2*(w-1) → (M5.ConditionalResidueCount.feasible w F (u.take (w-1)) (u.drop (w-1)) a b ↔ M5.ArithmeticResidueRecovery.wordValid w F (M5.ArithmeticResidueRecovery.completionWord (w-1) u a b))
