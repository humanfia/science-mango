import FrozenTarget_a405899fd2f97c5a
theorem M7.GeneratedFamily.family_range : QuantumHarnessFrozenTarget := by
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
