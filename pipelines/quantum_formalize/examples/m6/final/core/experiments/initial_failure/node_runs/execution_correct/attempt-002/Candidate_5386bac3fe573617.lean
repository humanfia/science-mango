import FrozenTarget_5386bac3fe573617
theorem M6.Final.execution_correct : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.ExecutionCorrect N a b
  intro N inst a b h
  have hb := M6.ActualTransfer.boundary_indexed_resources
  have hc := M6.ActualTransfer.character_indexed_resources
  have ho := M6.ActualTransfer.shifted_output_exact
  have hs := M6.ActualTransfer.shifted_scan_exact
  first
  | have hd := M6.SolveResources.actual_distance_work
  | have hd := M6.Solve.actual_distance_work
  | have hd := M6.QueryResources.actual_distance_work
  | have hd := M6.Query.actual_distance_work
  | have hd := M6.Postprocessing.actual_distance_work
  | have hd := M6.ActualTransfer.actual_distance_work
  | have hd := M6.Final.actual_distance_work
  | have hd := M6.actual_distance_work
  first
  | have hw := M6.SolveResources.actual_witness_work
  | have hw := M6.Solve.actual_witness_work
  | have hw := M6.QueryResources.actual_witness_work
  | have hw := M6.Query.actual_witness_work
  | have hw := M6.Postprocessing.actual_witness_work
  | have hw := M6.ActualTransfer.actual_witness_work
  | have hw := M6.Final.actual_witness_work
  | have hw := M6.actual_witness_work
  unfold M6.Final.Admissible at h
  unfold M6.Final.ExecutionCorrect
  aesop (add safe apply [hb, hc, ho, hs, hd, hw])
