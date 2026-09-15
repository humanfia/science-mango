import FrozenTarget_4b92e8dd9b330d67
theorem M5.PrefixPartition.count_partition : QuantumHarnessFrozenTarget := by
  change ∀ (α : Type) [Fintype α] [DecidableEq α] (W : Finset (List α)) (m : ℕ) (p : List α), (∀ q ∈ W, q.length = m) → p.length < m → M5.PrefixPartition.count W p = ∑ a : α, M5.PrefixPartition.count W (p ++ [a])
  intro α _ _ W m p hm hp
  classical
  by_cases hW : W = ∅
  · subst W
    simp [M5.PrefixPartition.count]
  obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hW
  have h₀ : p.length < q₀.length := by rw [hm q₀ hq₀]; exact hp
  let f : List α → α := fun q => if h : p.length < q.length then q.get ⟨p.length, h⟩ else q₀.get ⟨p.length, h₀⟩
  have hfiber (a : α) :
      (W.filter (fun q => p.IsPrefix q)).filter (fun q => f q = a) =
        W.filter (fun q => (p ++ [a]).IsPrefix q) := by
    ext q
    simp only [Finset.mem_filter]
    by_cases hq : q ∈ W
    · have hlt : p.length < q.length := by rw [hm q hq]; exact hp
      simp only [hq, true_and]
      rw [M5.PrefixPartition.prefix_next α p q a hlt]
      simp [f, hlt]
    · simp [hq]
  have hn : (W.filter (fun q => p.IsPrefix q)).card =
      ∑ a : α, (W.filter (fun q => (p ++ [a]).IsPrefix q)).card := by
    calc
      _ = ∑ a : α, ((W.filter (fun q => p.IsPrefix q)).filter (fun q => f q = a)).card :=
        Finset.card_eq_sum_card_fiberwise
          (f := f) (t := Finset.univ) (by intro q hq; exact Finset.mem_univ _)
      _ = _ := Finset.sum_congr rfl (fun a _ => congrArg Finset.card (hfiber a))
  change ((W.filter (fun q => p.IsPrefix q)).card : ℤ) =
    ∑ a : α, ((W.filter (fun q => (p ++ [a]).IsPrefix q)).card : ℤ)
  exact_mod_cast hn
