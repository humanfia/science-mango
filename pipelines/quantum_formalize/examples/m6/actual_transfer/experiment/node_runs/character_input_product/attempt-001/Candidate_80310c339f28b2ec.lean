import FrozenTarget_80310c339f28b2ec
theorem M6.ActualTransfer.character_input_product : QuantumHarnessFrozenTarget := by
  classical
  intro R N inst a b ha hb hRN P h
  rw [M6.ActualTransfer.product_halves]
  refine Finset.prod_bij (fun i _ => -i) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj hij
    exact neg_injective hij
  · intro j hj
    exact ⟨-j, Finset.mem_univ _, neg_neg j⟩
  · intro i hi
    simp [M6.ActualTransfer.characterWeight,
      M6.Transfer.output_convolution,
      M6.ActualTransfer.window_conv R N a ha hRN,
      M6.ActualTransfer.window_conv R N b hb hRN,
      M6.Physical.J, M6.Physical.boundary, M6.Physical.rev, mul_comm]
