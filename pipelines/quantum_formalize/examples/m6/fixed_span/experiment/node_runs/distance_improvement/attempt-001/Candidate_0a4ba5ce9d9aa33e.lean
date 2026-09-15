import FrozenTarget_0a4ba5ce9d9aa33e
theorem M6.FixedSpan.distance_improvement : QuantumHarnessFrozenTarget := by
  change ∀ R : ℕ, Filter.Tendsto (fun N : ℕ => (N : ℝ)^3 * (4 : ℝ)^R / (4 : ℝ)^N) Filter.atTop (nhds 0)
  intro R
  have h := tendsto_pow_const_div_const_pow_of_one_lt 3 (r := (4 : ℝ)) (by norm_num)
  simpa only [zero_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h.mul_const ((4 : ℝ)^R)
