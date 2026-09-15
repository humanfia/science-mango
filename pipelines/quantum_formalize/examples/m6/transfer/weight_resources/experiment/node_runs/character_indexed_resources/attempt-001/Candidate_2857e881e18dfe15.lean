import FrozenTarget_2857e881e18dfe15
theorem M6.ActualTransfer.character_indexed_resources : QuantumHarnessFrozenTarget := by
  intro N inst a b P h
  refine M6.Transfer.indexed_array_correct_resources (M6.ActualTransfer.span a b) N (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P) h ?_ ?_
  · intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).1
  · intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).2
