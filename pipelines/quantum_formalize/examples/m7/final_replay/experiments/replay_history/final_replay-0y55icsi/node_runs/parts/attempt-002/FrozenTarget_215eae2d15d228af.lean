import M7FinalReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), ∀ c : M7.FinalReplay.Certificate N w q, (M7.FinalReplay.check q c = Except.ok true ↔ M7.DefaultQuery.valid N q ∧ M7.GenerationReplay.check w (M7.QuerySectors.effective N q) c.generation = true ∧ M7.FactorReplay.check (M6.Cyclic.modulus N) c.factors = true ∧ c.generation.finalBases = (M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)).finalBases ∧ (∀ i, M7.LabelReplay.check (M7.FinalSelector.family N w q i) (c.labels i) = true) ∧ M7.QueryCertificate.check q (M7.FinalSelector.family N w q) c.query = Except.ok true)
