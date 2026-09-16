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
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → (M8.Solver.run c = M8.Solver.Outcome.unrecognized (M8.PhysicalBridge.signature c) ↔ M8.PhysicalBridge.signature c ≠ 1 ∧ M8.Cutoff.limit N < M8.OrbitSpan.value c)
