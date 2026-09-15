import M7FinalResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (E : Finset M5.BinaryPolynomial), 0 < w → w ≤ N → M7.PrefixSector.ValidSector N E → (M7.CompactGeneration.generate (N := N) w E).finalBases.card = M7.GeneratedFamily.size N w E ∧ (M7.GenerationCalls.generateMeasured (N := N) w E).2.root + (M7.GenerationCalls.generateMeasured (N := N) w E).2.children = (1 + M7.GeneratedFamily.size N w E * (2*M7.PrefixBits.depth N+1)) ∧ (M7.GenerationCalls.generateMeasured (N := N) w E).2.orbitCounts ≤ M7.GeneratedFamily.size N w E*(1 + M7.GeneratedFamily.size N w E * (2*M7.PrefixBits.depth N+1))
