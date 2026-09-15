import FrozenTarget_8331ecb97766297b
theorem M7.GeneratedFamily.family_range : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E hw hwN hE b
  have hfold {α : Type} (f : α → M7.Action.Recipe N) (l : List α)
      (s : Finset (M7.Action.Recipe N)) :
      b ∈ l.foldl (fun t e => insert (f e) t) s ↔
        b ∈ s ∨ ∃ e ∈ l, f e = b := by
    induction l generalizing s with
    | nil => simp
    | cons a l ih =>
        simp only [List.foldl_cons, ih, Finset.mem_insert, List.mem_cons]
        aesop
  change b ∈ (M7.CompactGeneration.generate (N := N) w E).finalBases ↔
    ∃ i : Fin (M7.CompactGeneration.generate (N := N) w E).emitted.length,
      ((M7.CompactGeneration.generate (N := N) w E).emitted.get i).representative = b
  rw [← List.exists_mem_iff_get]
  simp only [M7.CompactGeneration.generate, M7.CompactGeneration.run_fold,
    hfold, Finset.mem_empty, false_or]
