import M6FixedSpan


def QuantumHarnessFrozenTarget : Prop :=
  ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^3 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)
