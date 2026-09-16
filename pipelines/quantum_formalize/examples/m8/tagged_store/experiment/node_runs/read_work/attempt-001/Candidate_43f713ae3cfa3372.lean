import FrozenTarget_43f713ae3cfa3372
theorem M8.TaggedStore.read_work : QuantumHarnessFrozenTarget := by
  change ∀ (B : ℕ) (key : M8.TaggedStore.Tag) (s : M8.TaggedStore.Store), key.length ≤ B → (∀ r ∈ s, r.1.length ≤ B) → (M8.TaggedStore.read key s).2 ≤ s.length * (4 * (B + 1)) + 1
  have hflat (t : List Bool) :
      (t.flatMap (fun b => [true, b])).length = 2 * t.length := by
    induction t with
    | nil => simp
    | cons b bs ih =>
        simp [List.flatMap_cons, ih, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  intro B key s hk
  induction s with
  | nil =>
      intro hs
      simp [M8.TaggedStore.read]
  | cons r rs ih =>
      intro hs
      have hr : r.1.length ≤ B := hs r (by simp)
      have ht := ih (by
        intro x hx
        exact hs x (by simp [hx]))
      have hc := (M8.TaggedStore.comparison_exact key r.1).2
      have he : (M8.TaggedStore.recordBits r).length = 2 * r.1.length + 2 := by
        simp [M8.TaggedStore.recordBits, hflat]
      simp only [M8.TaggedStore.read, List.length_cons]
      split <;> simp only [Prod.snd] <;> nlinarith
