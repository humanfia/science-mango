import FrozenTarget_df1b71daeda429fb
theorem M8.TaggedStore.read_work : QuantumHarnessFrozenTarget := by
  change ∀ (B : ℕ) (key : M8.TaggedStore.Tag) (s : M8.TaggedStore.Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → (M8.TaggedStore.read key s).2 ≤ s.length * (4 * (B + 1)) + 1
  have hflat : ∀ t : List Bool, (t.flatMap (fun b => [true, b])).length = 2 * t.length := by
    intro t
    induction t with
    | nil => simp
    | cons b bs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
        omega
  intro B key s hk
  induction s with
  | nil => simp [M8.TaggedStore.read]
  | cons r rs ih =>
      intro hs
      have hr : r.1.length ≤ B := hs r (by simp)
      have ht : ∀ t ∈ rs, t.1.length ≤ B := by
        intro t ht
        exact hs t (by simp [ht])
      have hrest := ih ht
      have hc := (M8.TaggedStore.comparison_exact key r.1).2
      have hl : (M8.TaggedStore.recordBits r).length = 2 * r.1.length + 2 := by
        simp [M8.TaggedStore.recordBits, hflat]
      have hcharge : (M8.TaggedStore.recordBits r).length + (M8.TaggedStore.compare key r.1).2 + 1 ≤ 4 * (B + 1) := by
        omega
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      simp only [M8.TaggedStore.read]
      split <;> simp only [Prod.snd] <;> omega
