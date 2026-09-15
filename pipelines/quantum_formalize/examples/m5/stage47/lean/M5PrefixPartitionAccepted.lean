import M5PrefixPartition

theorem M5.PrefixPartition.count_empty : ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ) := by
  change ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ)
  intro α W
  classical
  simp [M5.PrefixPartition.count]

theorem M5.PrefixPartition.count_terminal : ∀ (α : Type) [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length = m → M5.PrefixPartition.count W p = (if p ∈ W then 1 else 0) := by
  intro α inst W m p hW hp
  classical
  have hcount : M5.PrefixPartition.count W p = ((W.filter (fun q => p.IsPrefix q)).card : ℤ) := by
    unfold M5.PrefixPartition.count
    apply congrArg (fun s : Finset (List α) => (s.card : ℤ))
    ext q
    simp only [Finset.mem_filter]
  have hf : W.filter (fun q => p.IsPrefix q) = W.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q hq
    constructor
    · intro h
      exact (h.eq_of_length (hp.trans (hW q hq).symm)).symm
    · intro h
      subst q
      exact List.prefix_refl p
  rw [hcount, hf]
  by_cases h : p ∈ W
  · have hs : W.filter (fun q => q = p) = {p} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hq => hq.2
      · intro hq
        subst q
        exact ⟨h, rfl⟩
    rw [hs]
    simp [h]
  · simp [h]

theorem M5.PrefixPartition.prefix_next : ∀ (α : Type) (p q : List α) (a : α) (h : p.length < q.length), (p ++ [a]).IsPrefix q ↔ p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a := by
  change ∀ (α : Type) (p q : List α) (a : α) (h : p.length < q.length), (p ++ [a]).IsPrefix q ↔ p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a
  intro α p q a h
  constructor
  · rintro ⟨s, rfl⟩
    constructor
    · exact ⟨[a] ++ s, by simp [List.append_assoc]⟩
    · simp [List.get_eq_getElem, List.append_assoc, List.getElem_append]
  · rintro ⟨hp, ha⟩
    simpa only [ha] using (List.concat_get_prefix hp h)

theorem M5.PrefixPartition.count_partition : ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a]) := by
  change ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a])
  intro α _ _ W m p hW hp
  classical
  have hc : (W.filter (fun q => p.IsPrefix q)).card =
      ∑ a : α, (W.filter (fun q => (p ++ [a]).IsPrefix q)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    have h : p.length < q.length := by
      rw [hW q hq]
      exact hp
    have hn : ∀ a : α, (p ++ [a]).IsPrefix q ↔
        p.IsPrefix q ∧ q.get ⟨p.length, h⟩ = a :=
      fun a => M5.PrefixPartition.prefix_next α p q a h
    simp only [hn]
    by_cases hpq : p.IsPrefix q
    · simp [hpq]
    · simp [hpq]
  have hcount : ∀ p : List α, M5.PrefixPartition.count W p = ((W.filter (fun q => p.IsPrefix q)).card : ℤ) := by
    intro p
    unfold M5.PrefixPartition.count
    apply congrArg (fun s : Finset (List α) => (s.card : ℤ))
    ext q
    simp only [Finset.mem_filter]
  simp only [hcount]
  exact_mod_cast hc
