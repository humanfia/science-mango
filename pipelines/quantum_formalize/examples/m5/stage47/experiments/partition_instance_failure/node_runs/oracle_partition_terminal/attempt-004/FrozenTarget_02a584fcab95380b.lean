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

theorem M5.ArithmeticResidueRecovery.completion_feasible : ∀ (T w : ℕ) (F : M5.BinaryPolynomial) (u : List (Fin T)) (a : Fin ((w-1) - (u.take (w-1)).length) → Fin T) (b : Fin ((w-1) - (u.drop (w-1)).length) → Fin T), u.length ≤ 2*(w-1) → (M5.ConditionalResidueCount.feasible w F (u.take (w-1)) (u.drop (w-1)) a b ↔ M5.ArithmeticResidueRecovery.wordValid w F (M5.ArithmeticResidueRecovery.completionWord (w-1) u a b)) := by
  intro T w F u a b hu
  classical
  rcases M5.ArithmeticResidueRecovery.completion_word_split (w - 1) u a b hu with
    ⟨hlen, hprefix, htake, hdrop⟩
  have ha := M5.ArithmeticResidueRecovery.prefix_algebra T _ (u.take (w - 1)) a
  have hb := M5.ArithmeticResidueRecovery.prefix_algebra T _ (u.drop (w - 1)) b
  simp only [M5.ArithmeticResidueRecovery.wordValid,
    M5.ConditionalResidueCount.feasible,
    hlen, htake, hdrop,
    M5.ConditionalResidueCount.selectedGcd,
    ha.1, ha.2, hb.1, hb.2,
    Nat.gcd_assoc, Nat.gcd_comm, Nat.gcd_left_comm]
  rfl

theorem M5.ArithmeticResidueRecovery.completion_prefix_card : ∀ {α : Type} [Fintype α] [DecidableEq α] (k : ℕ) (u : List α) (Valid : List α → Prop), u.length ≤ 2*k → M5.ArithmeticResidueRecovery.completionCount k u Valid = M5.PrefixPartition.count (M5.ArithmeticResidueRecovery.fullWords (2*k) Valid) u := by
  intro α instF instD k u Valid hu
  letI : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  classical
  have reprList : ∀ (v : List α) (m : ℕ), v.length = m → ∃ f : Fin m → α, List.ofFn f = v := by
    intro v m hm
    subst m
    exact ⟨v.get, List.ofFn_get v⟩
  have memFull : ∀ v : List α,
      v ∈ M5.ArithmeticResidueRecovery.fullWords (2*k) Valid ↔ v.length = 2*k ∧ Valid v := by
    intro v
    unfold M5.ArithmeticResidueRecovery.fullWords
    constructor
    · intro hv
      rcases Finset.mem_filter.mp hv with ⟨hm, hV⟩
      rcases Finset.mem_image.mp hm with ⟨f, _, hf⟩
      subst v
      exact ⟨List.length_ofFn, hV⟩
    · rintro ⟨hlen, hV⟩
      obtain ⟨f, hf⟩ := reprList v (2*k) hlen
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨f, Finset.mem_univ _, hf⟩, hV⟩
  unfold M5.ArithmeticResidueRecovery.completionCount M5.PrefixPartition.count
  apply congrArg (fun n : ℕ => (n : ℤ))
  refine Finset.card_bij (fun ab _ => M5.ArithmeticResidueRecovery.completionWord k u ab.1 ab.2) ?_ ?_ ?_
  · intro ab hab
    have hV := (Finset.mem_filter.mp hab).2
    have hs := M5.ArithmeticResidueRecovery.completion_word_split k u ab.1 ab.2 hu
    exact Finset.mem_filter.mpr ⟨(memFull _).mpr ⟨hs.1, hV⟩, hs.2.1⟩
  · intro ab hab cd hcd heq
    have ha := M5.ArithmeticResidueRecovery.completion_word_split k u ab.1 ab.2 hu
    have hc := M5.ArithmeticResidueRecovery.completion_word_split k u cd.1 cd.2 hu
    apply Prod.ext
    · apply List.ofFn_injective
      apply List.append_cancel_left (as := u.take k)
      exact ha.2.2.1.symm.trans ((congrArg (List.take k) heq).trans hc.2.2.1)
    · apply List.ofFn_injective
      apply List.append_cancel_left (as := u.drop k)
      exact ha.2.2.2.symm.trans ((congrArg (List.drop k) heq).trans hc.2.2.2)
  · intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hfull, hpre⟩
    rcases (memFull v).mp hfull with ⟨hlen, hV⟩
    have hpa := hpre.take k
    have hpb := hpre.drop k
    let ta := (v.take k).drop (u.take k).length
    let tb := (v.drop k).drop (u.drop k).length
    have hta : ta.length = k - (u.take k).length := by
      simp only [ta, List.length_drop, List.length_take, hlen]
      congr 1
      omega
    have htb : tb.length = k - (u.drop k).length := by
      simp only [tb, List.length_drop, hlen]
      congr 1
      omega
    obtain ⟨a, ha⟩ := reprList ta (k - (u.take k).length) hta
    obtain ⟨b, hb⟩ := reprList tb (k - (u.drop k).length) htb
    have heq : M5.ArithmeticResidueRecovery.completionWord k u a b = v := by
      unfold M5.ArithmeticResidueRecovery.completionWord
      rw [ha, hb]
      change (u.take k ++ (v.take k).drop (u.take k).length) ++
        (u.drop k ++ (v.drop k).drop (u.drop k).length) = v
      rw [← List.prefix_append_drop hpa, ← List.prefix_append_drop hpb]
      exact List.take_append_drop k v
    refine ⟨(a, b), ?_, heq⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, heq.symm ▸ hV⟩

theorem M5.ArithmeticResidueRecovery.oracle_prefix_count : ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → ∀ (u : List (Fin (M5.signaturePeriod F))), u.length ≤ 2*(w-1) → M5.ArithmeticResidueRecovery.oracle w F u = M5.PrefixPartition.count (M5.ArithmeticResidueRecovery.fullWords (2*(w-1)) (M5.ArithmeticResidueRecovery.wordValid w F)) u := by
  intro w F hw hF hF0 u hu
  classical
  have hfit : M5.ConditionalResidueCount.fits w (u.take (w - 1)) (u.drop (w - 1)) := by
    unfold M5.ConditionalResidueCount.fits
    simp only [List.length_take, List.length_drop]
    omega
  rw [← M5.ArithmeticResidueRecovery.completion_prefix_card (w - 1) u
    (M5.ArithmeticResidueRecovery.wordValid w F) hu]
  unfold M5.ArithmeticResidueRecovery.oracle
  rw [(M5.ConditionalResidueCount.period_conditionalA_exact w F
    (u.take (w - 1)) (u.drop (w - 1)) hw hF hF0).1]
  unfold M5.ArithmeticResidueRecovery.completionCount
  apply congrArg (fun n : ℕ => (n : ℤ))
  apply congrArg Finset.card
  unfold M5.ConditionalResidueCount.validCompletions
  rw [if_pos hfit]
  ext ab
  constructor
  · intro h
    have hF := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (M5.ArithmeticResidueRecovery.completion_feasible
        (M5.signaturePeriod F) w F u ab.1 ab.2 hu).mp hF⟩
  · intro h
    have hV := (Finset.mem_filter.mp h).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (M5.ArithmeticResidueRecovery.completion_feasible
        (M5.signaturePeriod F) w F u ab.1 ab.2 hu).mpr hV⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → (∀ (u : List (Fin (M5.signaturePeriod F))), u.length < 2*(w-1) → M5.ArithmeticResidueRecovery.oracle w F u = ∑ a : Fin (M5.signaturePeriod F), M5.ArithmeticResidueRecovery.oracle w F (u ++ [a])) ∧ (∀ (u : List (Fin (M5.signaturePeriod F))), u.length = 2*(w-1) → 0 < M5.ArithmeticResidueRecovery.oracle w F u → M5.ArithmeticResidueRecovery.wordValid w F u)
