import FrozenTarget_e8d833d9b6d60903
theorem M6.ActualTransfer.boundary_input_product : QuantumHarnessFrozenTarget := by
  classical
  intro R N inst a b ha hb hRN P h
  rw [← M6.Character.pinned_product, M6.ActualTransfer.product_halves]
  apply Finset.prod_congr rfl
  intro i hi
  simp [M6.ActualTransfer.boundaryWeight, M6.Physical.boundary,
    M6.Transfer.output_convolution,
    M6.ActualTransfer.window_conv R N a ha hRN,
    M6.ActualTransfer.window_conv R N b hb hRN]
