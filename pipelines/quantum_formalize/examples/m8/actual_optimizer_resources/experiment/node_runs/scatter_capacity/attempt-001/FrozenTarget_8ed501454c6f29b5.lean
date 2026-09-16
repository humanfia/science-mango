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
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → ∀ (start : M6.Transfer.Memory (M6.ActualTransfer.span a b)) (i : ℕ), i < N → ∀ (k : ℕ) (addr : M6.Transfer.CoefficientAddress (M6.ActualTransfer.span a b) N), (((M6.Transfer.scatterEventList (M6.ActualTransfer.span a b) N).take k).foldl (M6.Transfer.scatterUpdate ((M8.OptimizerResources.weight N a b pins character) i) (M6.Transfer.scalarLayers (N:=N) (M8.OptimizerResources.weight N a b pins character) start i)) (fun _ => 0) addr).natAbs < 2^(4*(N+1)) ∧ ∀ e : M6.Transfer.ScatterEvent (M6.ActualTransfer.span a b) N, (M6.Transfer.eventTerm ((M8.OptimizerResources.weight N a b pins character) i) (M6.Transfer.scalarLayers (N:=N) (M8.OptimizerResources.weight N a b pins character) start i) e).natAbs < 2^(4*(N+1))
