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

theorem M7.FinalReplay.checked_sets : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true → c.query.winners = M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) ∧ c.query.presentations = M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true → c.query.winners = M7.GlobalQuery.winners q (M7.FinalSelector.family N w q) ∧ c.query.presentations = M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N w inst q hw hwN c hc
  rcases (M7.FinalReplay.parts N w q c).mp hc with ⟨hv, hg, hf, hb, hl, hq⟩
  exact (M7.QueryCertificate.check_sound _ N q (M7.FinalSelector.family N w q) c.query hq).2
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true → ∀ y : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q y ↔ ∃ x ∈ c.query.winners, M7.FinalSelector.realize q x = y
