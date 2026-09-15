import FrozenTarget_2eb98d68297a6e69
theorem M7.GlobalQuery.same_class_presentation : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro H N inst q bases x hx
  classical
  have hs := M7.ActualPresentation.leastAction_spec N (bases x.1) (M7.GlobalQuery.realize bases x)
  cases he : M7.ActualPresentation.leastAction (bases x.1) (M7.GlobalQuery.realize bases x) with
  | none =>
      exact False.elim ((hs.2.mp he) ⟨x.2, rfl⟩)
  | some g =>
      have hg := ((hs.1 g).mp he).1
      have hw : (x.1, g) ∈ M7.GlobalQuery.winners q bases :=
        (M7.GlobalQuery.winning_fiber H N q bases x (x.1, g) rfl hg.symm).mp hx
      refine ⟨g, ⟨?_, hg⟩, ?_⟩
      · change (x.1, g) ∈ M7.GlobalQuery.winners q bases ∧
          M7.ActualPresentation.leastAction (bases x.1) (M7.Action.act g (bases x.1)) = some g
        refine ⟨hw, ?_⟩
        rw [hg]
        exact he
      · intro h hh
        have hhleast : M7.ActualPresentation.leastAction (bases x.1)
            (M7.Action.act h (bases x.1)) = some h := hh.1.2
        rw [hh.2] at hhleast
        exact Option.some.inj (hhleast.symm.trans he)
