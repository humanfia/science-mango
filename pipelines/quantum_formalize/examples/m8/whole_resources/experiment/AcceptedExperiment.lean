import M8WholeResources

theorem M8.WholeResources.charge_length : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).charges.length ≤ 6 := by
  intro N inst c
  classical
  unfold M8.WholeResources.run
  simp only
  split
  · simp only [List.length_cons, List.length_nil]
    omega
  · try simp only
    split
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · try simp only
      split
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega

theorem M8.WholeResources.elementary_bounds : ∀ (N : ℕ) [NeZero N], M8.WholeResources.setupWork N ≤ 21000*(N+1)^3 ∧ M8.WholeResources.transformWork N ≤ 96*(N+1)^3 ∧ M8.WholeResources.undoWork N ≤ 160*(N+1)^3 := by
  intro N inst
  have hfold (l : List ℕ) (w k : ℕ) :
      l.foldl (fun acc _ => acc + k) w = w + l.length * k := by
    induction l generalizing w with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons, ih]
      ring
  have hp := M8.BankLayout.payload_bound N
  simp only [M8.WholeResources.setupWork, M8.WholeResources.inputScanWork,
    M8.WholeResources.connectivityScanWork, M8.WholeResources.transformWork,
    M8.WholeResources.undoWork, hfold, List.length_range, zero_add]
  refine ⟨?_, ?_, ?_⟩ <;>
    nlinarith [Nat.zero_le (N^3), Nat.zero_le (N^2)]

theorem M8.WholeResources.noLogical_early : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.originalF c = 1 → (M8.WholeResources.run c).charges = [M8.WholeResources.setupWork N,M8.WholeResources.originalWork c] ∧ (M8.WholeResources.run c).discoveryCalls = 0 ∧ (M8.WholeResources.run c).optimizerCalls = 0 := by
  let QuantumHarnessFrozenTarget : Prop := (
    ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.originalF c = 1 → (M8.WholeResources.run c).charges = [M8.WholeResources.setupWork N,M8.WholeResources.originalWork c] ∧ (M8.WholeResources.run c).discoveryCalls = 0 ∧ (M8.WholeResources.run c).optimizerCalls = 0
  )
  change QuantumHarnessFrozenTarget
  unfold QuantumHarnessFrozenTarget
  intro N inst c h
  simp [M8.WholeResources.run, h]

theorem M8.WholeResources.original_preprocess_bound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.WholeResources.originalWork c ≤ 180*(N+1)^3 := by
  intro N inst c
  have ha := Nat.le_of_lt (M7.Supports.degree_lt N c.1)
  have hb := Nat.le_of_lt (M7.Supports.degree_lt N c.2)
  have hm := le_of_eq (M6.Coordinates.modulus_monic_degree N).2
  exact (M6.Euclid.preprocess_correct_cost N
    (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)
    (M6.Cyclic.modulus N) ha hb hm).2

theorem M8.WholeResources.projection : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).outcome = M8.Solver.run c := by
  classical
  intro N inst c
  change (M8.WholeResources.run c).outcome = M8.Solver.run c
  by_cases h : M8.Solver.originalF c = 1
  · simp [M8.WholeResources.run, M8.Solver.run, h]
  · simp only [M8.WholeResources.run, M8.Solver.run, h, if_false,
      M8.DiscoveryResources.projection]
    cases hd : M8.Discovery.discover c with
    | none => simp [hd]
    | some choice =>
      simp only [hd]
      cases hs : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
      | none => simp [hs]
      | some result =>
        rcases result with ⟨d, v, k⟩
        simp [hs]

theorem M8.WholeResources.selected_span : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ∀ choice : M8.Discovery.Choice N, M8.Discovery.discover c = some choice → M6.ActualTransfer.span (M7.Supports.polynomial (M8.Discovery.transformed c choice).1) (M7.Supports.polynomial (M8.Discovery.transformed c choice).2) ≤ M8.Cutoff.limit N := by
  intro N inst c w hw hc choice hchoice
  have hv : M8.PhysicalBridge.Valid w (M8.Discovery.transformed c choice) := by
    unfold M8.Discovery.transformed
    unfold M8.PhysicalBridge.Valid at *
    aesop (add safe apply [M7.Action.support_cards, M7.Connectivity.connected_action]) (add simp [M7.Action.support_cards, M7.Connectivity.connected_action])
  exact (M8.Solver.literal_span_le N (M8.Discovery.transformed c choice) w hw hv).trans
    (M8.Discovery.cutoff N c choice hchoice)

theorem M8.WholeResources.single_calls : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).discoveryCalls ≤ 1 ∧ (M8.WholeResources.run c).optimizerCalls ≤ (M8.WholeResources.run c).discoveryCalls := by
  classical
  intro N inst c
  change (M8.WholeResources.run c).discoveryCalls ≤ 1 ∧ (M8.WholeResources.run c).optimizerCalls ≤ (M8.WholeResources.run c).discoveryCalls
  by_cases h : M8.Solver.originalF c = 1
  · simp [M8.WholeResources.run, h]
  · cases hs : (M8.DiscoveryResources.run c).selected.map Prod.snd with
    | none => simp [M8.WholeResources.run, h, hs]
    | some choice =>
      cases ho : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
      | none => simp [M8.WholeResources.run, h, hs, ho]
      | some result =>
        rcases result with ⟨d, v, k⟩
        simp [M8.WholeResources.run, h, hs, ho]

theorem M8.WholeResources.indexed_work_bound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M8.WholeResources.indexedWork c ≤ 225000*(N+1)^6 := by
  classical
  intro N inst c w hw hc
  have hp (k : ℕ) : (N+1)^k ≤ (N+1)^(k+1) := by
    rw [pow_succ]
    nlinarith only [Nat.zero_le (N * (N+1)^k)]
  have h36 : (N+1)^3 ≤ (N+1)^6 := (hp 3).trans ((hp 4).trans (hp 5))
  have h56 : (N+1)^5 ≤ (N+1)^6 := hp 5
  rcases M8.WholeResources.elementary_bounds N with ⟨hs, ht, hu⟩
  have ho := M8.WholeResources.original_preprocess_bound N c
  have hs6 := hs.trans (Nat.mul_le_mul_left 21000 h36)
  have ht6 := ht.trans (Nat.mul_le_mul_left 96 h36)
  have hu6 := hu.trans (Nat.mul_le_mul_left 160 h36)
  have ho6 := ho.trans (Nat.mul_le_mul_left 180 h36)
  have hd : M8.DiscoveryResources.charged N (M8.DiscoveryResources.run c) ≤ 320*(N+1)^6 := by
    exact M8.DiscoveryResources.work_bound N c
  by_cases hf : M8.Solver.originalF c = 1
  · simp only [M8.WholeResources.indexedWork, M8.WholeResources.run, hf,
      ite_true, List.sum_cons, List.sum_nil, add_zero]
    omega
  · cases hchoice : (M8.DiscoveryResources.run c).selected.map Prod.snd with
    | none =>
        simp only [M8.WholeResources.indexedWork, M8.WholeResources.run, hf,
          ite_false, hchoice, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        omega
    | some choice =>
        have hdiscover : M8.Discovery.discover c = some choice :=
          (M8.DiscoveryResources.projection N c).symm.trans hchoice
        have hspan := M8.WholeResources.selected_span N c w hw hc choice hdiscover
        cases hsolve : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
        | none =>
            have hdist := M8.OptimizerResources.distance_work N
              (M7.Supports.polynomial (M8.Discovery.transformed c choice).1)
              (M7.Supports.polynomial (M8.Discovery.transformed c choice).2) hspan
            have hdist6 := hdist.trans (Nat.mul_le_mul_left 50000 h56)
            simp only [M8.WholeResources.indexedWork, M8.WholeResources.run, hf,
              ite_false, hchoice, hsolve, List.sum_append, List.sum_cons,
              List.sum_nil, add_zero]
            omega
        | some result =>
            rcases result with ⟨d, v, k⟩
            have hwitness := M8.OptimizerResources.witness_work N
              (M7.Supports.polynomial (M8.Discovery.transformed c choice).1)
              (M7.Supports.polynomial (M8.Discovery.transformed c choice).2)
              d v k hspan hsolve
            simp only [M8.WholeResources.indexedWork, M8.WholeResources.run, hf,
              ite_false, hchoice, hsolve, List.sum_append, List.sum_cons,
              List.sum_nil, add_zero]
            omega
#print axioms M8.WholeResources.charge_length
#print axioms M8.WholeResources.elementary_bounds
#print axioms M8.WholeResources.noLogical_early
#print axioms M8.WholeResources.original_preprocess_bound
#print axioms M8.WholeResources.projection
#print axioms M8.WholeResources.selected_span
#print axioms M8.WholeResources.indexed_work_bound
#print axioms M8.WholeResources.single_calls
