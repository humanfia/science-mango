import FrozenTarget_406b047271e0b2d9
theorem M6.Transfer.array_trace_inputs : QuantumHarnessFrozenTarget := by
  classical
  intro R N instN K instK W
  rw [M6.Transfer.array_trace_matrix R K W N,
    M6.Transfer.labelled_trace R N K W]
  exact M6.Transfer.indexed_weight_sum R N K (fun i => W i.val)
