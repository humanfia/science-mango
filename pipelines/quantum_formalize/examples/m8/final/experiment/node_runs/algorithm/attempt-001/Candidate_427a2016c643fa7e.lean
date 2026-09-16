import FrozenTarget_427a2016c643fa7e
theorem M8.Final.algorithm : QuantumHarnessFrozenTarget := by
  change M8.Final.Algorithm
  unfold M8.Final.Algorithm
  exact ⟨M8.Solver.output_gcd, M8.Solver.noLogical_exact, M8.Solver.unrecognized_exact, M8.Solver.recognized_exact, M8.Solver.recognized_correct⟩
