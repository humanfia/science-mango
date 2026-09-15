import M7FinalReplay

theorem M7.FinalReplay.invalid_rejection : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), ¬ M7.DefaultQuery.valid N q → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.error M7.DefaultQuery.QueryError.invalidSignature := by
  intro N w inst q hq c
  simp only [M7.FinalReplay.check, if_neg hq]

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

theorem M7.FinalReplay.exists_certificate : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∃ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → M7.DefaultQuery.valid N q → ∃ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q hw hwN hv
  have hE : M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q) := by
    apply M7.QuerySectors.effective_valid
    assumption
  have hm : (M6.Cyclic.modulus N).Monic := by
    first
    | simpa [M6.Cyclic.modulus] using (Polynomial.monic_X_pow_add_C (1 : ZMod 2) (NeZero.ne N))
    | have hn : -(1 : M5.BinaryPolynomial) = 1 := by
        have h : -(1 : ZMod 2) = 1 := by decide
        simpa only [map_neg, map_one] using congrArg (Polynomial.C : ZMod 2 → M5.BinaryPolynomial) h
      simpa [M6.Cyclic.modulus, sub_eq_add_neg, hn] using (Polynomial.monic_X_pow_sub_C (1 : ZMod 2) (NeZero.ne N))
  obtain ⟨d, hd⟩ := (M7.QueryCertificate.check_exact _ N q
    (M7.FinalSelector.family N w q)
    (M7.GlobalQuery.winners q (M7.FinalSelector.family N w q))
    (M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q))).mpr ⟨hv, rfl, rfl⟩
  let c : M7.FinalReplay.Certificate N w q :=
    { generation := M7.CompactGeneration.generate (N := N) w (M7.QuerySectors.effective N q)
      factors := M7.FactorReplay.expected (M6.Cyclic.modulus N)
      labels := fun i => M7.LabelReplay.expected (M7.FinalSelector.family N w q i)
      query := ⟨M7.GlobalQuery.winners q (M7.FinalSelector.family N w q),
        M7.QueryCertificate.allPresentations q (M7.FinalSelector.family N w q), d⟩ }
  refine ⟨c, (M7.FinalReplay.parts N w q c).mpr ?_⟩
  refine ⟨hv, ?_, ?_, rfl, ?_, hd⟩
  · exact M7.GenerationReplay.generate_checked N w (M7.QuerySectors.effective N q) hE
  · exact M7.FactorReplay.self_check (M6.Cyclic.modulus N) hm
  · intro i
    exact M7.LabelReplay.self_check N (M7.FinalSelector.family N w q i)

theorem M7.FinalReplay.physical_labels : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true → ∀ i : Fin (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)), ((c.labels i).answer = none ↔ (M7.RecipeSignature.signature (M7.FinalSelector.family N w q i)).natDegree = 0) ∧ (∀ (d k : ℕ) (v : M6.Pinned.Vector (2*N)), (c.labels i).answer = some (d,v,k) → M7.DefaultQuery.distance (M7.FinalSelector.family N w q i) = some d ∧ v ∈ M7.Transport.LX (M7.FinalSelector.family N w q i) ∧ M6.Pinned.weight v = d ∧ M6.Flatten.J N v ∈ M7.Transport.LZ (M7.FinalSelector.family N w q i) ∧ M6.Pinned.weight (M6.Flatten.J N v) = d ∧ k ≤ 2*N) := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true → ∀ i : Fin (M7.GeneratedFamily.size N w (M7.QuerySectors.effective N q)), ((c.labels i).answer = none ↔ (M7.RecipeSignature.signature (M7.FinalSelector.family N w q i)).natDegree = 0) ∧ (∀ (d k : ℕ) (v : M6.Pinned.Vector (2*N)), (c.labels i).answer = some (d,v,k) → M7.DefaultQuery.distance (M7.FinalSelector.family N w q i) = some d ∧ v ∈ M7.Transport.LX (M7.FinalSelector.family N w q i) ∧ M6.Pinned.weight v = d ∧ M6.Flatten.J N v ∈ M7.Transport.LZ (M7.FinalSelector.family N w q i) ∧ M6.Pinned.weight (M6.Flatten.J N v) = d ∧ k ≤ 2*N)
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  classical
  intro N w inst q hw hwN c hc i
  have hp := (M7.FinalReplay.parts N w q c).mp hc
  have hE : M7.PrefixSector.ValidSector N (M7.QuerySectors.effective N q) := by
    apply M7.QuerySectors.effective_valid
    exact hp.1
  have hg := (M7.GeneratedFamily.family_good N w (M7.QuerySectors.effective N q) hw hwN hE i).1
  have ha := M7.GeneratedFamily.family_anchored N w (M7.QuerySectors.effective N q) hw hwN hE i
  have hl := hp.2.2.2.2.1 i
  apply M7.LabelReplay.checked_physical_answer N w (M7.FinalSelector.family N w q i) (c.labels i)
  all_goals
    simp only [M7.FinalSelector.family, M7.PrefixOrbit.ClassValid] at *
    aesop

theorem M7.FinalReplay.raw_winners : ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true → ∀ y : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q y ↔ ∃ x ∈ c.query.winners, M7.FinalSelector.realize q x = y := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N w : ℕ) [NeZero N] (q : M7.DefaultQuery.Query), 0 < w → w ≤ N → ∀ c : M7.FinalReplay.Certificate N w q, M7.FinalReplay.check q c = Except.ok true → ∀ y : M7.Action.Recipe N, M7.FinalSelector.RawWinner w q y ↔ ∃ x ∈ c.query.winners, M7.FinalSelector.realize q x = y
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N w inst q hw hwN c hc y
  have hv := ((M7.FinalReplay.parts N w q c).mp hc).1
  have hW := (M7.FinalReplay.checked_sets N w q hw hwN c hc).1
  rw [hW]
  simpa [M7.FinalSelector.win, M7.StreamingIndices.stream_winners] using
    (M7.FinalSelector.raw_output N w q hw hwN hv y)
#print axioms M7.FinalReplay.invalid_rejection
#print axioms M7.FinalReplay.parts
#print axioms M7.FinalReplay.checked_sets
#print axioms M7.FinalReplay.exists_certificate
#print axioms M7.FinalReplay.physical_labels
#print axioms M7.FinalReplay.raw_winners
