import FrozenTarget_fce730aecdbdcdaa
theorem M7.GeneratedFamily.family_range : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E hw hwN hE b
  have fold_mem : ∀ {α : Type} (f : α → M7.Action.Recipe N) (l : List α)
      (s : Finset (M7.Action.Recipe N)),
      b ∈ l.foldl (fun s e => insert (f e) s) s ↔
        b ∈ s ∨ ∃ e ∈ l, f e = b := by
    intro α f l
    induction l with
    | nil => simp
    | cons e l ih =>
      intro s
      simp only [List.foldl_cons, ih, Finset.mem_insert, List.mem_cons]
      aesop
  have hfold :
      (M7.CompactGeneration.generate (N := N) w E).finalBases =
      (M7.CompactGeneration.generate (N := N) w E).emitted.foldl
        (fun s e => insert e.representative s) ∅ := by
    unfold M7.CompactGeneration.generate
    first
    | apply M7.CompactGeneration.run_fold
    | symm; apply M7.CompactGeneration.run_fold
  rw [hfold, fold_mem]
  simp only [Finset.not_mem_empty, false_or]
  constructor
  · rintro ⟨e, he, hb⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
    refine ⟨i, ?_⟩
    change ((M7.CompactGeneration.generate (N := N) w E).emitted.get i).representative = b
    rw [hi]
    exact hb
  · rintro ⟨i, hi⟩
    refine ⟨(M7.CompactGeneration.generate (N := N) w E).emitted.get i, ?_, hi⟩
    exact List.mem_iff_get.mpr ⟨i, rfl⟩
