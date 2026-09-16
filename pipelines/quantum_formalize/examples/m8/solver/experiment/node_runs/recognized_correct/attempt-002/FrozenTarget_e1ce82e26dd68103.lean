import M8Solver

theorem M8.Solver.originalF_signature : ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.originalF c = M8.PhysicalBridge.signature c := by
  intro N inst c
  have ha := Nat.le_of_lt (M7.Supports.degree_lt N c.1)
  have hb := Nat.le_of_lt (M7.Supports.degree_lt N c.2)
  have hm := le_of_eq (M6.Coordinates.modulus_monic_degree N).2
  have h := (M6.Euclid.preprocess_correct_cost N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) (M6.Cyclic.modulus N) ha hb hm).1
  simpa only [M8.Solver.originalF, M8.PhysicalBridge.signature, M7.RecipeSignature.signature, M6.Cyclic.signature, M6.Euclid.normalized_gcd, gcd_comm] using h
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ∀ (F : M8.Solver.BP) (d : ℕ) (z : M6.Pinned.Vector (2*N)) (choice : M8.Discovery.Choice N) (k : ℕ), M8.Solver.run c = M8.Solver.Outcome.recognized F d z choice k → F = M8.PhysicalBridge.signature c ∧ M8.Discovery.discover c = some choice ∧ M7.Transport.distance c = some d ∧ z ∈ M7.Transport.LX c ∧ M6.Pinned.weight z = d ∧ (∀ u ∈ M7.Transport.LX c, d ≤ M6.Pinned.weight u) ∧ k ≤ 2*N ∧ (∀ j : M8.Discovery.Choice N, M8.Discovery.Good c j → M8.Discovery.key choice ≤ M8.Discovery.key j) ∧ M6.Final.encodedQubits N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) = 2*F.natDegree
