import M8OptimizerResources

theorem M8.OptimizerResources.weight_bounds : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), ∀ i m t, M6.Transfer.polynomialMass ((M8.OptimizerResources.weight N a b pins character) i m t) ≤ 4 ∧ ((M8.OptimizerResources.weight N a b pins character) i m t).natDegree ≤ 2 := by
  intro N inst a b pins character i m t
  cases character with
  | false =>
      simp only [M8.OptimizerResources.weight, Bool.false_eq_true, if_false,
        M6.ActualTransfer.boundaryWeight]
      apply M6.Transfer.boundary_edge_bounds
  | true =>
      simp only [M8.OptimizerResources.weight, if_true,
        M6.ActualTransfer.characterWeight]
      apply M6.Transfer.character_edge_bounds
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → ∀ (k : ℕ) (d : Fin (2*N+1)), (((((Finset.univ : Finset (M6.Transfer.Memory (M6.ActualTransfer.span a b))).toList.take k).map (fun start => M6.Transfer.scalarLayers (N:=N) (M8.OptimizerResources.weight N a b pins character) start N (start,d))).sum)).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N ∧ (((((Finset.univ : Finset (M6.Transfer.Memory (M6.ActualTransfer.span a b))).toList.take k).map (fun start => M6.Transfer.scalarLayers (N:=N) (M8.OptimizerResources.weight N a b pins character) start N (start,d))).sum)).natAbs < 2^(4*(N+1))
