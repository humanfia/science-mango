import M6WeightResources

theorem M6.ActualTransfer.boundary_indexed_resources : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.span a b < N → M6.Transfer.IndexedArrayGuarantee (M6.ActualTransfer.span a b) N (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P) := by
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

theorem M6.ActualTransfer.character_indexed_resources : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.span a b < N → M6.Transfer.IndexedArrayGuarantee (M6.ActualTransfer.span a b) N (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P) := by
  intro N inst a b P h
  refine M6.Transfer.indexed_array_correct_resources (M6.ActualTransfer.span a b) N (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P) h ?_ ?_
  · intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).1
  · intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).2
#print axioms M6.ActualTransfer.boundary_indexed_resources
#print axioms M6.ActualTransfer.character_indexed_resources
