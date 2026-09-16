import FrozenTarget_acbb00162146c7ca
theorem M8.WholeResources.indexed_work_bound : QuantumHarnessFrozenTarget := by
  classical
  intro N inst c w hw hc
  have h36 : (N+1)^3 ≤ (N+1)^6 := by
    have hp : 0 < (N+1)^3 := by positivity
    calc
      (N+1)^3 = (N+1)^3 * 1 := by ring
      _ ≤ (N+1)^3 * (N+1)^3 := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hp)
      _ = (N+1)^6 := by ring
  have h56 : (N+1)^5 ≤ (N+1)^6 := by
    calc
      (N+1)^5 = (N+1)^5 * 1 := by ring
      _ ≤ (N+1)^5 * (N+1) := Nat.mul_le_mul_left _ (by omega)
      _ = (N+1)^6 := by ring
  obtain ⟨hs, ht, hu⟩ := M8.WholeResources.elementary_bounds N
  have ho := M8.WholeResources.original_preprocess_bound N c
  have hs' := hs.trans (Nat.mul_le_mul_left 21000 h36)
  have ht' := ht.trans (Nat.mul_le_mul_left 96 h36)
  have hu' := hu.trans (Nat.mul_le_mul_left 160 h36)
  have ho' := ho.trans (Nat.mul_le_mul_left 180 h36)
  have hd : M8.DiscoveryResources.charged N (M8.DiscoveryResources.run c) ≤ 320*(N+1)^6 :=
    M8.DiscoveryResources.work_bound N c
  by_cases hf : M8.Solver.originalF c = 1
  · simp only [M8.WholeResources.indexedWork, M8.WholeResources.run, hf, if_pos,
      List.sum_cons, List.sum_nil, add_zero]
    omega
  · cases hchoice : (M8.DiscoveryResources.run c).selected.map Prod.snd with
    | none =>
      simp only [M8.WholeResources.indexedWork, M8.WholeResources.run, hf, if_neg,
        hchoice, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      omega
    | some choice =>
      have hdiscover : M8.Discovery.discover c = some choice :=
        (M8.DiscoveryResources.projection N c).symm.trans hchoice
      have hspan := M8.WholeResources.selected_span N c w hw hc choice hdiscover
      cases hsolve : M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) with
      | none =>
        have hb := M8.OptimizerResources.distance_work N
          (M7.Supports.polynomial (M8.Discovery.transformed c choice).1)
          (M7.Supports.polynomial (M8.Discovery.transformed c choice).2) hspan
        have hb' := hb.trans (Nat.mul_le_mul_left 50000 h56)
        simp only [M8.WholeResources.indexedWork, M8.WholeResources.run, hf, if_neg,
          hchoice, hsolve, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        omega
      | some result =>
        rcases result with ⟨d, v, k⟩
        have hactual : M6.ActualTransfer.solve N
            (M7.Supports.polynomial (M8.Discovery.transformed c choice).1)
            (M7.Supports.polynomial (M8.Discovery.transformed c choice).2) = some (d,v,k) := by
          simpa only [M8.PhysicalBridge.solve] using hsolve
        have hb := M8.OptimizerResources.witness_work N
          (M7.Supports.polynomial (M8.Discovery.transformed c choice).1)
          (M7.Supports.polynomial (M8.Discovery.transformed c choice).2)
          d v k hspan hactual
        simp only [M8.WholeResources.indexedWork, M8.WholeResources.run, hf, if_neg,
          hchoice, hsolve, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        omega
