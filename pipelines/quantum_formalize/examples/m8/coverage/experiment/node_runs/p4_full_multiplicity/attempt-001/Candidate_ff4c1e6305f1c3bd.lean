import FrozenTarget_ff4c1e6305f1c3bd
theorem M8.Coverage.p4_full_multiplicity : QuantumHarnessFrozenTarget := by
  intro N inst hN v m hv hm hEq
  have hEven : Even N := by
    cases v with
    | zero => omega
    | succ k =>
      refine ⟨2^k*m, ?_⟩
      rw [hEq, pow_succ]
      ring
  constructor
  · exact M8.P4Gcd.full_multiplicity N hN v m hv hm hEq
  · exact (M8.Coverage.p4_recognized N hN hEven).1
