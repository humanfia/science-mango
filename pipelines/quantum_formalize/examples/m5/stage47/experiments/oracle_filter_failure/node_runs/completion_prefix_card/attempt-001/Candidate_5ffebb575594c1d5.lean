import FrozenTarget_5ffebb575594c1d5
theorem M5.ArithmeticResidueRecovery.completion_prefix_card : QuantumHarnessFrozenTarget := by
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
