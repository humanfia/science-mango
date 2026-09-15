import M5PrefixPartition

theorem M5.PrefixPartition.count_empty : ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ) := by
  change ∀ (α : Type) (W : Finset (List α)), M5.PrefixPartition.count W [] = (W.card : ℤ)
  intro α W
  classical
  simp [M5.PrefixPartition.count]

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
#print axioms M5.PrefixPartition.count_empty
#print axioms M5.PrefixPartition.prefix_next
