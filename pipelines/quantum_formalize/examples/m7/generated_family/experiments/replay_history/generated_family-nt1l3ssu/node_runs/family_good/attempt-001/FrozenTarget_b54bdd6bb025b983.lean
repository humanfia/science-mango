import M7GeneratedFamily

theorem M7.GeneratedFamily.family_range : ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ b : M7.Action.Recipe N, b ∈ (M7.CompactGeneration.generate (N := N) w E).finalBases ↔ ∃ i : Fin (M7.GeneratedFamily.size N w E), M7.GeneratedFamily.family N w E i = b := by
  classical
  intro N w inst E hw hwN hE b
  have hfold : ∀ {α : Type} (f : α → M7.Action.Recipe N) (l : List α)
      (s : Finset (M7.Action.Recipe N)),
      b ∈ l.foldl (fun t e => insert (f e) t) s ↔
        b ∈ s ∨ ∃ e ∈ l, f e = b := by
    intro α f l
    induction l with
    | nil => intro s; simp
    | cons a l ih =>
      intro s
      simp only [List.foldl_cons, ih, Finset.mem_insert, List.mem_cons]
      aesop
  have hf : (M7.CompactGeneration.generate (N := N) w E).finalBases =
      (M7.CompactGeneration.generate (N := N) w E).emitted.foldl
        (fun t e => insert e.representative t) ∅ := by
    dsimp only [M7.CompactGeneration.generate]
    first
    | apply M7.CompactGeneration.run_fold
    | symm; apply M7.CompactGeneration.run_fold
  change b ∈ (M7.CompactGeneration.generate (N := N) w E).finalBases ↔
    ∃ i : Fin (M7.CompactGeneration.generate (N := N) w E).emitted.length,
      ((M7.CompactGeneration.generate (N := N) w E).emitted.get i).representative = b
  rw [hf, hfold]
  simp only [Finset.notMem_empty, false_or]
  constructor
  · rintro ⟨e, he, hb⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
    exact ⟨i, by simpa only [hi] using hb⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, List.get_mem _ i, hi⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → ∀ i : Fin (M7.GeneratedFamily.size N w E), M7.PrefixOrbit.ClassValid w (M7.GeneratedFamily.family N w E i) ∧ M7.CanonicalOuter.canonical (M7.GeneratedFamily.family N w E i) = M7.GeneratedFamily.family N w E i
