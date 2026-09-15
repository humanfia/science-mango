import FrozenTarget_2ce5a9c718ec38df
theorem M7.GeneratedFamily.family_meets : QuantumHarnessFrozenTarget := by
  classical
  intro N w inst E hw hwN hE i
  let e := (M7.CompactGeneration.generate (N := N) w E).emitted.get i
  have he : e ∈ (M7.CompactGeneration.generate (N := N) w E).emitted := List.get_mem _ _
  have hl : e.leaf ∈ M7.RecoveryPrefix.completed N w E [] := by
    apply M7.CompactCorrectness.run_leaves N w E hE ∅ _ _
      (M7.CompactCorrectness.initial N w E hE).1 rfl e
    exact he
  have hr := M7.CompactCorrectness.run_records N w E ∅ _ _ e he
  refine ⟨M7.Action.inverse e.action, ?_⟩
  change M7.RecipeSignature.signature (M7.Action.act (M7.Action.inverse e.action) e.representative) ∈ E
  rw [hr.2.1]
  have hq := ((M7.RawCoverage.root_membership N w E e.leaf).mp hl).1
  exact hq.2
