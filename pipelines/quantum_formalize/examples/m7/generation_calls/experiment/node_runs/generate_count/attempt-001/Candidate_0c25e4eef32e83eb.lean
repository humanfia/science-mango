import FrozenTarget_0c25e4eef32e83eb
theorem M7.GenerationCalls.generate_count : QuantumHarnessFrozenTarget := by
  intro N inst w E
  classical
  let root := M7.CompactGeneration.residual w E (∅ : Finset (M7.Action.Recipe N)) []
  have hp : (M7.GenerationCalls.generateMeasured (N := N) w E).1 = M7.CompactGeneration.generate (N := N) w E := by
    unfold M7.GenerationCalls.generateMeasured M7.CompactGeneration.generate
    exact M7.GenerationCalls.run_projection N w E _ _ _
  have hcount := M7.GenerationCalls.run_count N w E ∅ root.toNat root
  change (M7.GenerationCalls.generateMeasured (N := N) w E).2.root = (M7.GenerationCalls.generateMeasured (N := N) w E).1.emitted.length + 1 ∧ (M7.GenerationCalls.generateMeasured (N := N) w E).2.children = 2 * M7.PrefixBits.depth N * (M7.GenerationCalls.generateMeasured (N := N) w E).1.emitted.length at hcount
  have hs : (M7.GenerationCalls.generateMeasured (N := N) w E).2.root + (M7.GenerationCalls.generateMeasured (N := N) w E).2.children = 1 + (M7.CompactGeneration.generate (N := N) w E).emitted.length * (2 * M7.PrefixBits.depth N + 1) := by
    rw [hcount.1, hcount.2, hp]
    ring
  have hb := M7.GenerationCalls.run_orbit_bound N w E ∅ root.toNat root
  change (M7.GenerationCalls.generateMeasured (N := N) w E).2.orbitCounts ≤ (M7.GenerationCalls.generateMeasured (N := N) w E).1.finalBases.card * ((M7.GenerationCalls.generateMeasured (N := N) w E).2.root + (M7.GenerationCalls.generateMeasured (N := N) w E).2.children) at hb
  rw [hp, hs] at hb
  exact ⟨hp, hs, hb⟩
