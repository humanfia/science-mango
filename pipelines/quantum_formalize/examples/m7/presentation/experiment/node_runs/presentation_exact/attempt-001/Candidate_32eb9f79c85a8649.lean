import FrozenTarget_32eb9f79c85a8649
theorem M7.Presentation.presentation_exact : QuantumHarnessFrozenTarget := by
  classical
  intro κ σ τ X Y _ _ _ K S T l r m feasible objective mode a ha
  have had : a ∈ M7.Presentation.domain K S T :=
    (((M7.Selection.selector_exact (M7.Presentation.Record κ σ τ) m
      (M7.Presentation.domain K S T)
      (fun x => feasible (M7.Presentation.realize l r x))
      (fun x => objective (M7.Presentation.realize l r x)) mode).1 a).mp ha).1
  have hs := M7.Presentation.targetLeast_spec κ σ τ X Y K S T l r
    (M7.Presentation.realize l r a)
  cases he : M7.Presentation.targetLeast K S T l r (M7.Presentation.realize l r a) with
  | none =>
      exact False.elim ((hs.2.mp he) ⟨a, had, rfl⟩)
  | some b =>
      obtain ⟨hbd, hba, hmin⟩ := (hs.1 b).mp he
      have hb : b ∈ M7.Presentation.selected K S T l r feasible objective mode :=
        (M7.Presentation.winning_fiber κ σ τ X Y K S T l r m feasible objective mode
          a b had hbd hba.symm).mp ha
      refine ⟨b, ⟨?_, hba⟩, ?_⟩
      · simpa [M7.Presentation.present, hb, hba] using he
      · intro c hc
        have hct : M7.Presentation.targetLeast K S T l r
            (M7.Presentation.realize l r c) = some c := hc.1.2
        rw [hc.2, he] at hct
        exact (Option.some.inj hct).symm
