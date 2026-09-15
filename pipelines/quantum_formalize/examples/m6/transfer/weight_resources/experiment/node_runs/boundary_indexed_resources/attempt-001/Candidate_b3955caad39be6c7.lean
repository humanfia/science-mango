import FrozenTarget_b3955caad39be6c7
theorem M6.ActualTransfer.boundary_indexed_resources : QuantumHarnessFrozenTarget := by
  intro N inst a b P h
  refine M6.Transfer.indexed_array_correct_resources
    (M6.ActualTransfer.span a b) N
    (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P)
    h ?_ ?_
  · intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).1
  · intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).2
