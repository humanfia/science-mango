import M7FinalReplay

theorem M7.FinalReplay.parts : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), ∀ c : M7.FinalReplay.Certificate N w q, (M7.FinalReplay.check q c = Except.ok true ↔ M7.DefaultQuery.valid N q ∧ M7.GenerationReplay.check w (M7.QuerySectors.effective N q) c.generation = true ∧ M7.FactorReplay.check (M6.Cyclic.modulus N) c.factors = true ∧ c.generation.finalBases = (M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)).finalBases ∧ (∀ i, M7.LabelReplay.check (M7.FinalSelector.family N w q i) (c.labels i) = true) ∧ M7.QueryCertificate.check q (M7.FinalSelector.family N w q) c.query = Except.ok true) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), ∀ c : M7.FinalReplay.Certificate N w q, (M7.FinalReplay.check q c = Except.ok true ↔ M7.DefaultQuery.valid N q ∧ M7.GenerationReplay.check w (M7.QuerySectors.effective N q) c.generation = true ∧ M7.FactorReplay.check (M6.Cyclic.modulus N) c.factors = true ∧ c.generation.finalBases = (M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)).finalBases ∧ (∀ i, M7.LabelReplay.check (M7.FinalSelector.family N w q i) (c.labels i) = true) ∧ M7.QueryCertificate.check q (M7.FinalSelector.family N w q) c.query = Except.ok true)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q c
  by_cases hv : M7.DefaultQuery.valid N q
  · cases hq : M7.QueryCertificate.check q (M7.FinalSelector.family N w q) c.query with
    | error e =>
        simp [M7.FinalReplay.check, hv, hq]
    | ok b =>
        cases b <;>
          simp [M7.FinalReplay.check, hv, hq, M7.QueryCertificate.allOn, Bool.and_eq_true, and_assoc]
  · simp [M7.FinalReplay.check, hv]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true → ∀ i : Fin (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)), ((c.labels i).answer = none ↔ (M7.RecipeSignature.signature (M7.FinalSelector.family N w q i)).natDegree = 0) ∧ (∀ (d k : ℕ) (v : M6.Pinned.Vector (2*N)), (c.labels i).answer = some (d,v,k) → M7.DefaultQuery.distance (M7.FinalSelector.family N w q i) = some d ∧ v ∈ M7.Transport.LX (M7.FinalSelector.family N w q i) ∧ M6.Pinned.weight v = d ∧ M6.Flatten.J N v ∈ M7.Transport.LZ (M7.FinalSelector.family N w q i) ∧ M6.Pinned.weight (M6.Flatten.J N v) = d ∧ k ≤ 2*N)
