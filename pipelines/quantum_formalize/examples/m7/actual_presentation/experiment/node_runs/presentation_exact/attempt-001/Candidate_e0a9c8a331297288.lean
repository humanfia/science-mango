import FrozenTarget_e0a9c8a331297288
theorem M7.ActualPresentation.presentation_exact : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst c m feasible objective mode g hg
  classical
  cases hl : M7.ActualPresentation.leastAction c (M7.Action.act g c) with
  | none =>
      exact False.elim ((M7.ActualPresentation.leastAction_spec N c
        (M7.Action.act g c)).2.mp hl ⟨g, rfl⟩)
  | some h =>
      have heq : M7.Action.act h c = M7.Action.act g c :=
        ((M7.ActualPresentation.leastAction_spec N c
          (M7.Action.act g c)).1 h).mp hl |>.1
      have hw : h ∈ M7.ActualPresentation.selected c feasible objective mode :=
        (M7.ActualPresentation.winning_fiber N c m feasible objective mode h g heq).mpr hg
      refine ⟨h, ⟨?_, heq⟩, ?_⟩
      · unfold M7.ActualPresentation.present
        refine ⟨hw, ?_⟩
        rw [heq]
        exact hl
      · intro k hk
        have hkLeast : M7.ActualPresentation.leastAction c (M7.Action.act k c) = some k :=
          hk.1.2
        rw [hk.2] at hkLeast
        exact Option.some.inj (hkLeast.symm.trans hl)
