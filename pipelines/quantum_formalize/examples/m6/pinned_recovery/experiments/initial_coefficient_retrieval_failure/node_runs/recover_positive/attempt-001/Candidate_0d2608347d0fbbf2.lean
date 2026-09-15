import FrozenTarget_0d2608347d0fbbf2
theorem M6.Pinned.recover_positive : QuantumHarnessFrozenTarget := by
  change ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ), M6.Pinned.partitions c → ∀ (P : M6.Pinned.Pins m) (xs : List (Fin m)), 0 < c P → 0 < c (M6.Pinned.recover c P xs).1
  intro m c hc
  unfold M6.Pinned.partitions at hc
  have hchoose : ∀ (P : M6.Pinned.Pins m) (i : Fin m), 0 < c P → 0 < c (M6.Pinned.choose c P i).1 := by
    intro P i hP
    unfold M6.Pinned.choose
    split
    all_goals
      first
      | exact hP
      | (split <;> dsimp only <;>
          first
          | assumption
          | (have hsum := hc P i (by assumption)
             omega))
  intro P xs
  induction xs generalizing P with
  | nil =>
      simpa only [M6.Pinned.recover] using (fun h : 0 < c P => h)
  | cons i xs ih =>
      intro hP
      simpa only [M6.Pinned.recover] using
        (ih (M6.Pinned.choose c P i).1 (hchoose P i hP))
