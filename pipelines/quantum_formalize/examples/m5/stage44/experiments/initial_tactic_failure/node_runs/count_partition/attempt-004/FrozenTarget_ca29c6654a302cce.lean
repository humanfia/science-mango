import M5PrefixPartition

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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a])
