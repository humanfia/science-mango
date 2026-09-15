import FrozenTarget_89b433188cbe26c7
theorem M6.Transfer.actual_layer_intermediates : QuantumHarnessFrozenTarget := by
  classical
  intro R N W start i k addr hmass hdegree
  have hinput : M6.Transfer.arrayMass (M6.Transfer.scalarLayers (N := N) W start i) ≤ 8 ^ i := by
    rw [M6.Transfer.scalar_layers_exact R N W start i hdegree]
    exact (M6.Transfer.encoded_array_mass R N (M6.Transfer.layers W start i)).trans
      (M6.Transfer.layers_mass R W start i hmass)
  have hbound : 8 * M6.Transfer.arrayMass (M6.Transfer.scalarLayers (N := N) W start i) ≤ 8 ^ (i + 1) := by
    calc
      _ ≤ 8 * 8 ^ i := Nat.mul_le_mul_left 8 hinput
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  constructor
  · exact (M6.Transfer.scatter_prefix_magnitude R N (W i)
      (M6.Transfer.scalarLayers (N := N) W start i) k addr (hmass i)).trans hbound
  · intro e
    have he : (M6.Transfer.eventTerm (W i)
        (M6.Transfer.scalarLayers (N := N) W start i) e).natAbs ≤
        M6.Transfer.eventMass (W i) (M6.Transfer.scalarLayers (N := N) W start i) := by
      unfold M6.Transfer.eventMass
      exact Finset.single_le_sum
        (f := fun e : M6.Transfer.ScatterEvent R N =>
          (M6.Transfer.eventTerm (W i)
            (M6.Transfer.scalarLayers (N := N) W start i) e).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    exact he.trans ((M6.Transfer.event_mass_bound R N (W i)
      (M6.Transfer.scalarLayers (N := N) W start i) (hmass i)).trans hbound)
