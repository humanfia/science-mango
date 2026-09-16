import M8Solver

theorem M8.Solver.discovery_span : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → (M8.Discovery.discover c ≠ none ↔ M8.OrbitSpan.value c ≤ M8.Cutoff.limit N) := by
  intro N inst c w hw hv
  have hleft : c.1.Nonempty := Finset.card_pos.mp (by
    rw [hv.1]
    exact hw)
  have hright : c.2.Nonempty := Finset.card_pos.mp (by
    rw [hv.2.1]
    exact hw)
  exact (M8.Discovery.complete N c).trans
    (M8.OrbitSpan.small_iff N c hleft hright (M8.Cutoff.limit N)).symm

theorem M8.Solver.literal_span_le : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M6.ActualTransfer.span (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ≤ M8.Anchor.span c := by
  intro N inst c w hw hc
  classical
  have degree_bound (s : Finset (ZMod N)) (L : ℕ)
      (hs : ∀ i ∈ s, ZMod.val i ≤ L) :
      (M7.Supports.polynomial s).natDegree ≤ L := by
    by_cases hz : M7.Supports.polynomial s = 0
    · simp [hz]
    · have hm := Polynomial.natDegree_mem_support_of_nonzero hz
      rw [M7.Supports.support] at hm
      rcases Finset.mem_image.mp hm with ⟨i, hi, he⟩
      rw [← he]
      exact hs i hi
  have hb := (M8.Anchor.span_le N c (M8.Anchor.span c)).mp le_rfl
  change max (M7.Supports.polynomial c.1).natDegree
    (M7.Supports.polynomial c.2).natDegree ≤ M8.Anchor.span c
  exact max_le (degree_bound c.1 _ hb.1) (degree_bound c.2 _ hb.2)

theorem M8.Solver.optimizer_present : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.signature c ≠ 1 → ∀ choice : M8.Discovery.Choice N, M8.Discovery.discover c = some choice → M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) ≠ none := by
  intro N inst c w hw hvalid hsignature choice hdiscover hnone
  have hanchored : M8.PhysicalBridge.Anchored (M7.Action.act (M8.Discovery.action choice) c) :=
    M8.Discovery.anchored N c choice hdiscover
  exact hsignature ((M8.PhysicalBridge.noLogical N c (M8.Discovery.action choice) w hvalid hanchored).mp hnone)

theorem M8.Solver.originalF_signature : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.originalF c = M8.PhysicalBridge.signature c := by
  intro N inst c
  have ha := Nat.le_of_lt (M7.Supports.degree_lt N c.1)
  have hb := Nat.le_of_lt (M7.Supports.degree_lt N c.2)
  have hm := le_of_eq (M6.Coordinates.modulus_monic_degree N).2
  have h := (M6.Euclid.preprocess_correct_cost N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N) ha hb hm).1
  simpa only [M8.Solver.originalF, M8.PhysicalBridge.signature, M7.RecipeSignature.signature, M6.Cyclic.signature, M6.Euclid.normalized_gcd, gcd_comm] using h

theorem M8.Solver.noLogical_exact : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → (M8.Solver.run c = M8.Solver.Outcome.noLogical (M8.PhysicalBridge.signature c) ↔ M8.PhysicalBridge.signature c = 1) ∧ (M8.Solver.run c = M8.Solver.Outcome.noLogical (M8.PhysicalBridge.signature c) ↔ M7.Transport.distance c = none) := by
  intro N inst c w hw hc
  classical
  have hrun : M8.Solver.run c = M8.Solver.Outcome.noLogical (M8.PhysicalBridge.signature c) ↔ M8.PhysicalBridge.signature c = 1 := by
    by_cases hF : M8.PhysicalBridge.signature c = 1
    · simp [M8.Solver.run, M8.Solver.originalF_signature N c, hF]
    · cases hd : M8.Discovery.discover c with
      | none =>
          simp [M8.Solver.run, M8.Solver.originalF_signature N c, hF, hd]
      | some choice =>
          cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
          | none =>
              simp [M8.Solver.run, M8.Solver.originalF_signature N c, hF, hd, hs]
          | some result =>
              rcases result with ⟨d, v, k⟩
              simp [M8.Solver.run, M8.Solver.originalF_signature N c, hF, hd, hs]
  exact ⟨hrun, hrun.trans (M8.RawParameters.raw_noLogical N w c hw hc).1.symm⟩

theorem M8.Solver.output_gcd : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.outputF (M8.Solver.run c) = M8.PhysicalBridge.signature c := by
  change ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.outputF (M8.Solver.run c) = M8.PhysicalBridge.signature c
  intro N inst c
  classical
  by_cases h : M8.Solver.originalF c = 1
  · simpa [M8.Solver.run, h, M8.Solver.outputF] using M8.Solver.originalF_signature N c
  · cases hd : M8.Discovery.discover c with
    | none =>
        simpa [M8.Solver.run, h, hd, M8.Solver.outputF] using M8.Solver.originalF_signature N c
    | some choice =>
        cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
        | none =>
            simpa [M8.Solver.run, h, hd, hs, M8.Solver.outputF] using M8.Solver.originalF_signature N c
        | some result =>
            rcases result with ⟨d, v, k⟩
            simpa [M8.Solver.run, h, hd, hs, M8.Solver.outputF] using M8.Solver.originalF_signature N c

theorem M8.Solver.recognized_correct : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ∀ (F : M8.Solver.BP) (d : ℕ) (z : M6.Pinned.Vector (2*N)) (choice : M8.Discovery.Choice N) (k : ℕ), M8.Solver.run c = M8.Solver.Outcome.recognized F d z choice k → F = M8.PhysicalBridge.signature c ∧ M8.Discovery.discover c = some choice ∧ M7.Transport.distance c = some d ∧ z ∈ M7.Transport.LX c ∧ M6.Pinned.weight z = d ∧ (∀ u ∈ M7.Transport.LX c, d ≤ M6.Pinned.weight u) ∧ k ≤ 2*N ∧ (∀ j : M8.Discovery.Choice N, M8.Discovery.Good c j → M8.Discovery.key choice ≤ M8.Discovery.key j) ∧ M6.Final.encodedQubits N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) = 2*F.natDegree := by
  classical
  intro N inst c w hw hvalid F d z choice k hrun
  by_cases hOne : M8.Solver.originalF c = 1
  · simp [M8.Solver.run, hOne] at hrun
  · simp only [M8.Solver.run, if_neg hOne] at hrun
    cases hdiscover : M8.Discovery.discover c with
    | none => simp [hdiscover] at hrun
    | some chosen =>
      have hsig : M8.PhysicalBridge.signature c ≠ 1 := by
        intro hs
        apply hOne
        rw [M8.Solver.originalF_signature N c]
        exact hs
      have hanchor := M8.Discovery.anchored N c chosen hdiscover
      obtain ⟨d', v, k', hsolve, hdist, hmem, hweight, hmin, hbound⟩ :=
        M8.PhysicalBridge.minimum_original_witness N c
          (M8.Discovery.action chosen) w hvalid hanchor hsig
      change M8.PhysicalBridge.solve (M8.Discovery.transformed c chosen) =
        some (d', v, k') at hsolve
      simp only [hdiscover, hsolve] at hrun
      injection hrun with hF hd hz hc hk
      subst F
      subst d
      subst z
      subst choice
      subst k
      refine ⟨M8.Solver.originalF_signature N c, ?_, hdist, hmem,
        hweight, hmin, hbound, ?_, ?_⟩
      · first | exact hdiscover | rfl
      · exact M8.Discovery.lex_first N c chosen hdiscover
      · simpa only [M8.Solver.originalF_signature N c] using
          M8.RawParameters.encoded_dimension N w c hw hvalid

theorem M8.Solver.recognized_exact : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ((∃ (d : ℕ) (z : M6.Pinned.Vector (2*N)) (choice : M8.Discovery.Choice N) (k : ℕ), M8.Solver.run c = M8.Solver.Outcome.recognized (M8.PhysicalBridge.signature c) d z choice k) ↔ M8.PhysicalBridge.signature c ≠ 1 ∧ M8.OrbitSpan.value c ≤ M8.Cutoff.limit N) := by
  classical
  intro N inst c w hw hv
  constructor
  · rintro ⟨d, z, choice, k, hr⟩
    have hsig : M8.PhysicalBridge.signature c ≠ 1 := by
      intro hs
      simp [M8.Solver.run, M8.Solver.originalF_signature N c, hs] at hr
    refine ⟨hsig, (M8.Solver.discovery_span N c w hw hv).mp ?_⟩
    intro hn
    simp [M8.Solver.run, M8.Solver.originalF_signature N c, hsig, hn] at hr
  · rintro ⟨hsig, hspan⟩
    have hdiscover : M8.Discovery.discover c ≠ none :=
      (M8.Solver.discovery_span N c w hw hv).mpr hspan
    cases hd : M8.Discovery.discover c with
    | none => exact (hdiscover hd).elim
    | some choice =>
      have hsolve := M8.Solver.optimizer_present N c w hw hv hsig choice hd
      cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
      | none => exact (hsolve hs).elim
      | some result =>
        rcases result with ⟨d, v, k⟩
        refine ⟨d, M8.PhysicalBridge.undo (M8.Discovery.action choice) v, choice, k, ?_⟩
        simp [M8.Solver.run, M8.Solver.originalF_signature N c, hsig, hd, hs]

theorem M8.Solver.unrecognized_exact : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → (M8.Solver.run c = M8.Solver.Outcome.unrecognized (M8.PhysicalBridge.signature c) ↔ M8.PhysicalBridge.signature c ≠ 1 ∧ M8.Cutoff.limit N < M8.OrbitSpan.value c) := by
  classical
  intro N inst c w hw hv
  have hF := M8.Solver.originalF_signature N c
  have hspan := M8.Solver.discovery_span N c w hw hv
  by_cases hs : M8.PhysicalBridge.signature c = 1
  · simp [M8.Solver.run, hF, hs]
  · cases hd : M8.Discovery.discover c with
    | none =>
        have hlt : M8.Cutoff.limit N < M8.OrbitSpan.value c := by
          apply Nat.lt_of_not_ge
          intro hle
          exact (hspan.mpr hle) hd
        simp [M8.Solver.run, hF, hs, hd, hlt]
    | some choice =>
        have hle : M8.OrbitSpan.value c ≤ M8.Cutoff.limit N := by
          apply hspan.mp
          simp [hd]
        have hp := M8.Solver.optimizer_present N c w hw hv hs choice hd
        cases ho : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
        | none => exact False.elim (hp ho)
        | some result =>
            rcases result with ⟨d, v, k⟩
            simp [M8.Solver.run, hF, hs, hd, ho, not_lt_of_ge hle]
#print axioms M8.Solver.discovery_span
#print axioms M8.Solver.literal_span_le
#print axioms M8.Solver.optimizer_present
#print axioms M8.Solver.originalF_signature
#print axioms M8.Solver.noLogical_exact
#print axioms M8.Solver.output_gcd
#print axioms M8.Solver.recognized_correct
#print axioms M8.Solver.recognized_exact
#print axioms M8.Solver.unrecognized_exact
