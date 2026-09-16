import M8WholeResources

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

theorem M8.WholeResources.original_preprocess_bound : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.WholeResources.originalWork c ≤ 180*(N+1)^3 := by
  intro N inst c
  have ha := Nat.le_of_lt (M7.Supports.degree_lt N c.1)
  have hb := Nat.le_of_lt (M7.Supports.degree_lt N c.2)
  have hm := le_of_eq (M6.Coordinates.modulus_monic_degree N).2
  exact (M6.Euclid.preprocess_correct_cost N
    (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2)
    (M6.Cyclic.modulus N) ha hb hm).2

theorem M8.WholeResources.selected_span : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ∀ choice : M8.Discovery.Choice N, M8.Discovery.discover c = some choice → M6.ActualTransfer.span (M7.Supports.polynomial (M8.Discovery.transformed c choice).1) (M7.Supports.polynomial (M8.Discovery.transformed c choice).2) ≤ M8.Cutoff.limit N := by
  intro N inst c w hw hc choice hchoice
  have hv : M8.PhysicalBridge.Valid w (M8.Discovery.transformed c choice) := by
    unfold M8.Discovery.transformed
    unfold M8.PhysicalBridge.Valid at *
    aesop (add safe apply [M7.Action.support_cards, M7.Connectivity.connected_action]) (add simp [M7.Action.support_cards, M7.Connectivity.connected_action])
  exact (M8.Solver.literal_span_le N (M8.Discovery.transformed c choice) w hw hv).trans
    (M8.Discovery.cutoff N c choice hchoice)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M8.WholeResources.indexedWork c ≤ 225000*(N+1)^6
