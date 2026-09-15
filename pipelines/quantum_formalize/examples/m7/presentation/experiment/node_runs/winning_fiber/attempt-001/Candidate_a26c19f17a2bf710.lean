import FrozenTarget_a26c19f17a2bf710
theorem M7.Presentation.winning_fiber : QuantumHarnessFrozenTarget := by
  intro κ σ τ X Y _ _ _ K S T l r m feasible objective mode a b ha hb hab
  classical
  change a ∈ M7.Selection.select (M7.Presentation.domain K S T)
      (fun x => feasible (M7.Presentation.realize l r x))
      (fun x => objective (M7.Presentation.realize l r x)) mode ↔
    b ∈ M7.Selection.select (M7.Presentation.domain K S T)
      (fun x => feasible (M7.Presentation.realize l r x))
      (fun x => objective (M7.Presentation.realize l r x)) mode
  have hex := (M7.Selection.selector_exact (M7.Presentation.Record κ σ τ) m
    (M7.Presentation.domain K S T)
    (fun x => feasible (M7.Presentation.realize l r x))
    (fun x => objective (M7.Presentation.realize l r x)) mode).1
  rw [hex a, hex b]
  simp only [ha, hb, hab]
