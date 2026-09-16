import FrozenTarget_efae437201237844
theorem M8.TaggedStore.write_work : QuantumHarnessFrozenTarget := by
  change ∀ (B : ℕ) (key : M8.TaggedStore.Tag) (bit : Bool) (s : M8.TaggedStore.Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → (M8.TaggedStore.write key bit s).2 ≤ s.length * (4 * (B + 1)) + 1
  intro B key bit s hk
  have hflat : ∀ t : List Bool, (t.flatMap (fun b => [true, b])).length = 2 * t.length := by
    intro t
    induction t with
    | nil => simp
    | cons b t ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
        omega
  induction s with
  | nil =>
      intro hs
      simp [M8.TaggedStore.write]
  | cons r rs ih =>
      intro hs
      have hr : r.1.length ≤ B := hs r (by simp)
      have ht : ∀ x ∈ rs, x.1.length ≤ B := by
        intro x hx
        exact hs x (by simp [hx])
      have hi := ih ht
      have hc := (M8.TaggedStore.comparison_exact key r.1).2
      have hl : (M8.TaggedStore.recordBits r).length = 2 * r.1.length + 2 := by
        simp [M8.TaggedStore.recordBits, hflat]
      have hcharge : (M8.TaggedStore.recordBits r).length + (M8.TaggedStore.compare key r.1).2 + 1 ≤ 4 * (B + 1) := by
        omega
      simp only [M8.TaggedStore.write, List.length_cons, Nat.add_mul, Nat.one_mul]
      split <;> dsimp only <;> omega
