import FrozenTarget_ba29794143d16d58
theorem M7.CompactCorrectness.generate_exact : QuantumHarnessFrozenTarget := by
  intro N inst w E hE
  have hb := (M7.CompactCorrectness.initial N w E hE).1
  let root := M7.CompactGeneration.residual (N := N) w E ∅ []
  have hg := M7.CompactCorrectness.run_good N w E hE ∅ root.toNat root hb rfl
  have hz := M7.CompactCorrectness.run_zero N w E hE ∅ root.toNat root hb rfl (le_refl _)
  have hn := M7.CompactCorrectness.run_nodup N w E hE ∅ root.toNat root hb rfl
  simpa only [M7.CompactGeneration.generate, root] using
    And.intro hg (And.intro hz.1 (And.intro hz.2 hn))
