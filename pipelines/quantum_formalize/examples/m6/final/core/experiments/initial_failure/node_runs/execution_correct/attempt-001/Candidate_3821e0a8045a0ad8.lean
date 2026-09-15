import FrozenTarget_3821e0a8045a0ad8
theorem M6.Final.execution_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ExecutionCorrect N a b
  intro N inst a b h
  first
  | have hb := @M6.ActualTransfer.boundary_indexed_resources
  | have hb := @M6.Transfer.boundary_indexed_resources
  first
  | have hc := @M6.ActualTransfer.character_indexed_resources
  | have hc := @M6.Transfer.character_indexed_resources
  first
  | have ho := @M6.Postprocessing.shifted_output_exact
  | have ho := @M6.ActualTransfer.shifted_output_exact
  | have ho := @M6.Transfer.shifted_output_exact
  first
  | have hs := @M6.Postprocessing.shifted_scan_exact
  | have hs := @M6.ActualTransfer.shifted_scan_exact
  | have hs := @M6.Transfer.shifted_scan_exact
  first
  | have hd := @M6.SolveResources.actual_distance_work
  | have hd := @M6.Postprocessing.actual_distance_work
  | have hd := @M6.Transfer.actual_distance_work
  first
  | have hw := @M6.SolveResources.actual_witness_work
  | have hw := @M6.Postprocessing.actual_witness_work
  | have hw := @M6.Transfer.actual_witness_work
  unfold M6.Final.Admissible at h
  unfold M6.Final.ExecutionCorrect
  aesop
