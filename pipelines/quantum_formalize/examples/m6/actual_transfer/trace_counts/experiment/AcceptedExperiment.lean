import M6TraceCountsReady

theorem M6.ActualTransfer.boundary_trace_inputs : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.boundaryTrace N a b P = ∑ h : M6.Transfer.Input N, M6.Character.pinnedMonomial P (M6.Flatten.flatten N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) := by
  intro N inst a b hspan P
  classical
  unfold M6.ActualTransfer.boundaryTrace
  have hdeg : ∀ i m t,
      (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.boundaryWeight
    exact (M6.Transfer.boundary_edge_bounds (2 * N) P _ _ _ _).2
  rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg,
    M6.Transfer.array_trace_inputs]
  apply Finset.sum_congr rfl
  intro h hh
  exact M6.ActualTransfer.boundary_input_product
    (M6.ActualTransfer.span a b) N a b
    (by simpa only [M6.ActualTransfer.span] using (le_max_left a.natDegree b.natDegree))
    (by simpa only [M6.ActualTransfer.span] using (le_max_right a.natDegree b.natDegree))
    hspan P h

theorem M6.ActualTransfer.character_trace_inputs : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → ∀ P : M6.Pinned.Pins (2*N), M6.ActualTransfer.characterTrace N a b P = ∑ h : M6.Transfer.Input N, (∏ q : Fin (2*N), M6.Character.pinnedCharacterFactor P q (M6.Flatten.flatten N (M6.Physical.J N (M6.Physical.boundary N (M6.Coordinates.coefficients N a) (M6.Coordinates.coefficients N b) h)) q)) := by
  intro N inst a b hspan P
  classical
  have hdeg : ∀ i m t,
      (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
    intro i m t
    unfold M6.ActualTransfer.characterWeight
    exact (M6.Transfer.character_edge_bounds (2*N) P _ _ _ _).2
  unfold M6.ActualTransfer.characterTrace
  rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg,
    M6.Transfer.array_trace_inputs]
  apply Finset.sum_congr rfl
  intro h hh
  exact M6.ActualTransfer.character_input_product
    (M6.ActualTransfer.span a b) N a b
    (by unfold M6.ActualTransfer.span; exact le_max_left _ _)
    (by unfold M6.ActualTransfer.span; exact le_max_right _ _)
    hspan P h
#print axioms M6.ActualTransfer.boundary_trace_inputs
#print axioms M6.ActualTransfer.character_trace_inputs
